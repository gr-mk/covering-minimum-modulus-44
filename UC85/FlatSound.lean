import UC85.FlatDefs

/-! Combinatorial soundness of the origin checks (UC85 pilot). -/

namespace UC85
open Modulus40
namespace Env
variable {d : ℕ} (E : Env d)

/-! ## Combinatorial soundness -/

theorem eval_of_mem {a : ℕ → Bool} {c : RUP.Clause} {v : ℕ} {b : Bool}
    (hl : (v, b) ∈ c) (h : a v = b) : c.eval a = true := by
  simp only [Std.Sat.CNF.Clause.eval, List.any_eq_true]
  exact ⟨(v, b), hl, by simp [h]⟩

theorem aloOK_sound {x : Fin d → ℕ} (j : Fin d) (c : RUP.Clause)
    (hxj : x j < E.natoms j) (hT : (E.tmask j).testBit (x j) = true)
    (h : E.aloOK j c = true) : c.eval (fun v => (E.vinfo v).eval x) = true := by
  simp only [aloOK, List.all_eq_true, List.mem_range] at h
  have h1 := h (x j) hxj
  simp only [hT, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true] at h1
  obtain ⟨⟨v, b⟩, hl, hb, hat⟩ := h1
  simp only at hb hat
  subst hb
  apply eval_of_mem hl
  cases hv : E.vinfo v with
  | atom j' a' =>
    rw [hv] at hat
    simp only [isAtom, Bool.and_eq_true, beq_iff_eq] at hat
    obtain ⟨hj, ha⟩ := hat
    have hj' : j' = j := Fin.ext hj
    subst hj' ha
    simp [VarInfo.eval]
  | gate j' m => rw [hv] at hat; simp [isAtom] at hat
  | unused => rw [hv] at hat; simp [isAtom] at hat

theorem gateOK_sound {x : Fin d → ℕ} (c : RUP.Clause) (h : E.gateOK c = true) :
    c.eval (fun v => (E.vinfo v).eval x) = true := by
  simp only [gateOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hlen, h0⟩, h1⟩, hp⟩ := h
  have hm0 : c.getD 0 (0, false) ∈ c := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
  have hm1 : c.getD 1 (0, false) ∈ c := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem (by omega)
  generalize c.getD 0 (0, false) = l0 at hm0 h0 hp
  generalize c.getD 1 (0, false) = l1 at hm1 h1 hp
  obtain ⟨g, b0⟩ := l0
  obtain ⟨v, b1⟩ := l1
  simp only at h0 h1 hp
  subst h0 h1
  cases hg : E.vinfo g with
  | atom _ _ => rw [hg] at hp; simp [gatePair] at hp
  | unused => rw [hg] at hp; simp [gatePair] at hp
  | gate j m =>
    cases hv : E.vinfo v with
    | gate _ _ => rw [hg, hv] at hp; simp [gatePair] at hp
    | unused => rw [hg, hv] at hp; simp [gatePair] at hp
    | atom j' a =>
      rw [hg, hv] at hp
      simp only [gatePair, Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨hj, hma⟩ := hp
      have hj' : j' = j := (Fin.ext hj).symm
      subst hj'
      by_cases hxa : x j' = a
      · apply eval_of_mem hm0; simp [hg, VarInfo.eval, hxa, hma]
      · apply eval_of_mem hm1; simp [hv, VarInfo.eval, hxa]

theorem famOK_sound {x : Fin d → ℕ} (i : ℕ) (c : RUP.Clause)
    (hT : ∀ j, (E.tmask j).testBit (x j) = true)
    (hF : i < E.famCount → (∀ j, E.famIdx i j < (E.ld j).coordinates.length) →
      ∃ j, (E.fmask i j).testBit (x j) = false)
    (h : E.famOK i c = true) : c.eval (fun v => (E.vinfo v).eval x) = true := by
  simp only [famOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hi, hall⟩ := h
  have hj : ∀ j : Fin d, E.famAt i c j = true := fun j => by
    simpa [j.isLt] using hall j.val j.isLt
  have hbound : ∀ j, E.famIdx i j < (E.ld j).coordinates.length := fun j => by
    have := hj j; simp only [famAt, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  obtain ⟨j, hjf⟩ := hF hi hbound
  have hbad : (E.badAt i j).testBit (x j) = true := by
    simp [badAt, Nat.testBit_xor, hT j, hjf]
  have hj2 := hj j
  simp only [famAt, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq] at hj2
  rcases hj2.2 with h0 | hany
  · rw [h0] at hbad; simp at hbad
  obtain ⟨⟨v, b⟩, hl, hcov⟩ := List.any_eq_true.mp hany
  simp only [litCovers, Bool.and_eq_true, Bool.not_eq_true'] at hcov
  obtain ⟨hb, hcov⟩ := hcov
  subst hb
  apply eval_of_mem hl
  cases hv : E.vinfo v with
  | atom j' a =>
    rw [hv] at hcov
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcov
    obtain ⟨hjj, hna⟩ := hcov
    have hj' : j' = j := Fin.ext hjj
    subst hj'
    have hne : x j' ≠ a := fun hxa => by rw [hxa] at hbad; rw [hbad] at hna; simp at hna
    simp [VarInfo.eval, hne]
  | gate j' m =>
    rw [hv] at hcov
    simp only [Bool.and_eq_true, beq_iff_eq] at hcov
    obtain ⟨hjj, hzero⟩ := hcov
    have hj' : j' = j := Fin.ext hjj
    subst hj'
    have hm : m.testBit (x j') = false := by
      cases hmb : m.testBit (x j')
      · rfl
      · have h1 : (m &&& E.badAt i j').testBit (x j') = true := by
          simp [Nat.testBit_land, hmb, hbad]
        rw [hzero] at h1; simp at h1
    simp [VarInfo.eval, hm]
  | unused => rw [hv] at hcov; simp at hcov

theorem origin_sound (x : Fin d → ℕ) (hx : ∀ j, x j < E.natoms j)
    (hT : ∀ j, (E.tmask j).testBit (x j) = true)
    (hF : ∀ i < E.famCount, (∀ j, E.famIdx i j < (E.ld j).coordinates.length) →
      ∃ j, (E.fmask i j).testBit (x j) = false)
    (o : Origin d) (c : RUP.Clause) (h : E.originOK o c = true) :
    c.eval (fun v => (E.vinfo v).eval x) = true := by
  cases o with
  | alo j => exact E.aloOK_sound j c (hx j) (hT j) h
  | gate => exact E.gateOK_sound c h
  | fam i => exact E.famOK_sound i c hT (hF i) h

end Env
end UC85
