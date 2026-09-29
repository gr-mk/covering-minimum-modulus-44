import UC85.Flat
import UC85.BitRUP

/-!
# Section certificates with BitRUP steps, the SectionGlue lemma, and the box-tree walk

* `Env.cover_bit`: `Env.cover` with the bitmask RUP checker.
* `section_glue`: G1 (base ∪ targets = Z), G2 (targets covered, §3.4 up to its allowed holes),
  G3 (allowed holes inside later targets) give coverage of every integer.
* `walk`/`walk_sep`: a guillotine tree over exponent boxes, walked by each box from the root;
  two distinct boxes that both reach their own leaves are separated at their divergence node.
-/

namespace UC85
open Modulus40

namespace Env
variable {d : ℕ} (E : Env d)

theorem cover_bit (hvalid : ∀ j, (E.ld j).Valid) (hmask : ∀ j, MasksValid E.primes E.ld E.maskAt j)
    (htgt : ∀ j, E.tIdx j < (E.ld j).coordinates.length)
    (clauses : ℕ → RUP.Clause) (hints : ℕ → List ℕ) (origin : ℕ → Origin d)
    (initial count final : ℕ)
    (hO : ∀ i < initial, E.originOK (origin i) (clauses i) = true)
    (hsteps : ∀ i, initial ≤ i → i < count → BitRUP.StepValid clauses hints i)
    (hfinal : final < count) (hempty : clauses final = [])
    (z : ℤ) (hz : E.target.Matches E.primes z) :
    (∃ i < E.famCount, (E.fam i).Matches E.primes z) ∨
      ∃ j, ∃ r ∈ (E.ld j).rays, z = r.center := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hnc, hcen⟩ := hcon
  have hatom := fun j => E.exists_atom j (hvalid j) (hmask j).1 z (fun r hr h => hcen j r hr h)
  choose x hx using hatom
  have hbit : ∀ j k, k < (E.ld j).coordinates.length →
      ((E.maskAt j k).testBit (x j).val = true ↔ (E.coord j k).Matches (E.primes j) z) := by
    intro j k hk
    rw [(hmask j).2 k hk, Coordinate.mask_testBit]
    exact hx j _ (E.coord_mem hk)
  have hT : ∀ j, (E.tmask j).testBit (x j).val = true := fun j => (hbit j _ (htgt j)).2 (hz j)
  have hF : ∀ i < E.famCount, (∀ j, E.famIdx i j < (E.ld j).coordinates.length) →
      ∃ j, (E.fmask i j).testBit (x j).val = false := by
    intro i hi hb
    have hn := hnc i hi
    simp only [PrimePattern.Matches, not_forall] at hn
    obtain ⟨j, hj⟩ := hn
    refine ⟨j, ?_⟩
    cases h : (E.fmask i j).testBit (x j).val
    · rfl
    · exact absurd ((hbit j _ (hb j)).1 h) hj
  have hinit : ∀ i < initial,
      (clauses i).eval (fun v => (E.vinfo v).eval (fun j => (x j).val)) = true := fun i hi =>
    E.origin_sound (fun j => (x j).val) (fun j => (x j).isLt) hT hF (origin i) (clauses i) (hO i hi)
  have hall := BitRUP.clauses_true clauses hints initial count hsteps _ hinit final hfinal
  rw [hempty] at hall
  simp at hall

end Env

/-- **SectionGlue.** `Q` is "covered by a family or a ray centre"; targets `t < n4` are §3.4's. -/
theorem section_glue (Q : ℤ → Prop) (T A : ℕ → ℤ → Prop) (n4 nT nA : ℕ)
    (h1 : ∀ z, Q z ∨ ∃ t < nT, T t z)
    (h2a : ∀ t < n4, ∀ z, T t z → Q z ∨ ∃ a < nA, A a z)
    (h2b : ∀ t, n4 ≤ t → t < nT → ∀ z, T t z → Q z)
    (h3 : ∀ a < nA, ∀ z, A a z → Q z ∨ ∃ t, n4 ≤ t ∧ t < nT ∧ T t z) : ∀ z, Q z := by
  intro z
  rcases h1 z with hq | ⟨t, ht, hz⟩
  · exact hq
  by_cases h4 : t < n4
  · rcases h2a t h4 z hz with hq | ⟨a, ha, hza⟩
    · exact hq
    rcases h3 a ha z hza with hq | ⟨t', h4', ht', hz'⟩
    · exact hq
    · exact h2b t' h4' ht' z hz'
  · exact h2b t (Nat.le_of_not_gt h4) ht z hz

/-! ## Box tree: node codes `2*b+1` (leaf of box `b`) and `2*(c + 32*(t + 256*(l + 2^21*r)))`. -/

def goesLeft (s : SupportInterval) (t : ℕ) : Bool :=
  match s.hi with | some u => decide (u < t) | none => false

def goesRight (s : SupportInterval) (t : ℕ) : Bool := decide (t ≤ s.lo)

def walk {d : ℕ} (info : ℕ → ℕ) (box : ℕ → SupportBox d) (i : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, n =>
    if info n % 2 = 1 then info n / 2 == i
    else if h : info n / 2 % 32 < d then
      if goesLeft (box i ⟨info n / 2 % 32, h⟩) (info n / 64 % 256) then
        walk info box i f (info n / 16384 % 2097152)
      else if goesRight (box i ⟨info n / 2 % 32, h⟩) (info n / 64 % 256) then
        walk info box i f (info n / 34359738368)
      else false
    else false

theorem sep_of_sides {s u : SupportInterval} {t : ℕ} (hl : goesLeft s t = true)
    (hr : goesRight u t = true) : s.Separated u := by
  left
  unfold goesLeft at hl
  unfold goesRight at hr
  unfold SupportInterval.Before
  cases hs : s.hi with
  | none => simp [hs] at hl
  | some v => simp only [hs, decide_eq_true_eq] at hl hr ⊢; omega

theorem walk_sep {d : ℕ} {info : ℕ → ℕ} {box : ℕ → SupportBox d} {i j : ℕ} (hij : i ≠ j) :
    ∀ f n, walk info box i f n = true → walk info box j f n = true →
      (box i).Separated (box j) := by
  intro f
  induction f with
  | zero => intro n h; simp [walk] at h
  | succ f ih =>
    intro n hi hj
    simp only [walk] at hi hj
    by_cases hleaf : info n % 2 = 1
    · rw [if_pos hleaf, beq_iff_eq] at hi hj
      exact absurd (hi.symm.trans hj) hij
    rw [if_neg hleaf] at hi hj
    by_cases hc : info n / 2 % 32 < d
    swap
    · rw [dif_neg hc] at hi; simp at hi
    rw [dif_pos hc] at hi hj
    by_cases hLi : goesLeft (box i ⟨_, hc⟩) (info n / 64 % 256) = true <;>
      by_cases hLj : goesLeft (box j ⟨_, hc⟩) (info n / 64 % 256) = true
    · rw [if_pos hLi] at hi; rw [if_pos hLj] at hj; exact ih _ hi hj
    · rw [if_neg hLj] at hj
      by_cases hRj : goesRight (box j ⟨_, hc⟩) (info n / 64 % 256) = true
      · exact ⟨_, sep_of_sides hLi hRj⟩
      · rw [if_neg hRj] at hj; simp at hj
    · rw [if_neg hLi] at hi
      by_cases hRi : goesRight (box i ⟨_, hc⟩) (info n / 64 % 256) = true
      · exact ⟨_, Or.symm (sep_of_sides hLj hRi)⟩
      · rw [if_neg hRi] at hi; simp at hi
    · rw [if_neg hLi] at hi; rw [if_neg hLj] at hj
      by_cases hRi : goesRight (box i ⟨_, hc⟩) (info n / 64 % 256) = true
      swap
      · rw [if_neg hRi] at hi; simp at hi
      by_cases hRj : goesRight (box j ⟨_, hc⟩) (info n / 64 % 256) = true
      swap
      · rw [if_neg hRj] at hj; simp at hj
      rw [if_pos hRi] at hi; rw [if_pos hRj] at hj
      exact ih _ hi hj

theorem sep_of_walks {d k : ℕ} (info : ℕ → ℕ) (box : ℕ → SupportBox d) (F root : ℕ)
    (hw : ∀ i < k, walk info box i F root = true) :
    ∀ i j : Fin k, i ≠ j → (box i).Separated (box j) := fun i j hij =>
  walk_sep (fun h => hij (Fin.ext h)) F root (hw i i.isLt) (hw j j.isLt)

end UC85
