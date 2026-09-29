import UC85.FlatSound

/-! Arithmetic soundness: from a checked flat refutation to section coverage (UC85 pilot). -/

namespace UC85
open Modulus40
namespace Env
variable {d : ℕ} (E : Env d)

/-! ## Arithmetic soundness -/

theorem coord_mem {j : Fin d} {k : ℕ} (hk : k < (E.ld j).coordinates.length) :
    E.coord j k ∈ (E.ld j).coordinates := by
  unfold coord; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk

/-- A noncentral integer has an atom at each prime with the same coordinate tests. -/
theorem exists_atom (j : Fin d) (hvalid : (E.ld j).Valid) (hprime : (E.ld j).prime = E.primes j)
    (z : ℤ) (hcen : ∀ r ∈ (E.ld j).rays, z ≠ r.center) :
    ∃ k : Fin (E.ld j).representatives.length, ∀ s ∈ (E.ld j).coordinates,
      s.test (E.primes j) ((E.ld j).representatives.get k) = true ↔ s.Matches (E.primes j) z := by
  have hv := hvalid
  rcases hvalid with ⟨hp, -, -, -, -, ha, hg, -, -⟩
  have hz : ∀ s ∈ (E.ld j).coordinates, ¬ s.IsRayCenter z := by
    intro s hs hc
    cases s with
    | fixed e r => exact hc
    | ray f c dg => exact hcen _ (ha _ hs) hc
  obtain ⟨a, ha', hsig⟩ := (E.ld j).realizes hv z hz
  obtain ⟨k, rfl⟩ := List.get_of_mem ha'
  refine ⟨k, fun s hs => ?_⟩
  rw [← hprime, Coordinate.test_eq_true_iff hp s (hg s hs)]
  exact (hsig s hs).symm

/-- **Section coverage from a checked flat refutation.** Every integer of the target
pattern is matched by one of the first `famCount` families, or is a ray center. -/
theorem cover (hvalid : ∀ j, (E.ld j).Valid) (hmask : ∀ j, MasksValid E.primes E.ld E.maskAt j)
    (htgt : ∀ j, E.tIdx j < (E.ld j).coordinates.length)
    (clauses : ℕ → RUP.Clause) (hints : ℕ → List ℕ) (origin : ℕ → Origin d)
    (initial count final : ℕ)
    (hO : ∀ i < initial, E.originOK (origin i) (clauses i) = true)
    (hsteps : ∀ i, initial ≤ i → i < count → FastRUP.StepValid clauses hints i)
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
  have hT : ∀ j, (E.tmask j).testBit (x j).val = true := fun j =>
    (hbit j _ (htgt j)).2 (hz j)
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
  have hall := FastRUP.clauses_true clauses hints initial count hsteps _ hinit final hfinal
  rw [hempty] at hall
  simp at hall

/-- Every ray of the local table of prime `j` is the coordinate at `j` of a listed family. -/
def RaysOK (j : Fin d) (wit : List ℕ) : Bool :=
  (List.range (E.ld j).rays.length).all fun n =>
    decide (wit.getD n 0 < E.famCount) &&
      decide (E.fam (wit.getD n 0) j = .ray ((E.ld j).rays.getD n ⟨0, 0, 0, 0⟩).first
        ((E.ld j).rays.getD n ⟨0, 0, 0, 0⟩).center ((E.ld j).rays.getD n ⟨0, 0, 0, 0⟩).digit)

theorem center_of_raysOK {wit : Fin d → List ℕ} (hr : ∀ j, E.RaysOK j (wit j) = true)
    {z : ℤ} {j : Fin d} {r : Ray} (hmem : r ∈ (E.ld j).rays) (hz : z = r.center) :
    ∃ i < E.famCount, (E.fam i j).IsRayCenter z := by
  obtain ⟨n, rfl⟩ := List.get_of_mem hmem
  have h := hr j
  simp only [RaysOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, heq⟩ := h n.val n.isLt
  refine ⟨_, hlt, ?_⟩
  rw [heq, List.getD_eq_getElem _ _ n.isLt]
  simpa [Coordinate.IsRayCenter] using hz

/-- `cover` in the form consumed by `MainReduction` (`hcover`, restricted to the target). -/
theorem cover_main (hvalid : ∀ j, (E.ld j).Valid) (hmask : ∀ j, MasksValid E.primes E.ld E.maskAt j)
    (htgt : ∀ j, E.tIdx j < (E.ld j).coordinates.length)
    (wit : Fin d → List ℕ) (hr : ∀ j, E.RaysOK j (wit j) = true)
    (clauses : ℕ → RUP.Clause) (hints : ℕ → List ℕ) (origin : ℕ → Origin d)
    (initial count final : ℕ)
    (hO : ∀ i < initial, E.originOK (origin i) (clauses i) = true)
    (hsteps : ∀ i, initial ≤ i → i < count → FastRUP.StepValid clauses hints i)
    (hfinal : final < count) (hempty : clauses final = [])
    (z : ℤ) (hz : E.target.Matches E.primes z) :
    (∃ i : Fin E.famCount, (E.fam i).Matches E.primes z) ∨
      ∃ (i : Fin E.famCount) (j : Fin d), (E.fam i j).IsRayCenter z := by
  rcases E.cover hvalid hmask htgt clauses hints origin initial count final hO hsteps hfinal
    hempty z hz with ⟨i, hi, h⟩ | ⟨j, r, hr', hz'⟩
  · exact Or.inl ⟨⟨i, hi⟩, h⟩
  · obtain ⟨i, hi, h⟩ := E.center_of_raysOK hr hr' hz'
    exact Or.inr ⟨⟨i, hi⟩, j, h⟩

end Env
end UC85
