import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Finite distinct covering systems

Congruence classes are represented by a natural modulus and an integer residue.
Distinctness always means distinct **moduli**, not disjoint subsets of the integers.
The target statement includes a class of modulus exactly 40, not just a lower bound.
-/

namespace Modulus40

/-- One congruence class of integers. Positive moduli are required by `IsCoveringSystem`. -/
structure Congruence where
  modulus : ℕ
  residue : ℤ
  deriving DecidableEq, Repr

/-- Membership in the congruence class, for positive and negative integers alike. -/
def Congruence.Covers (c : Congruence) (z : ℤ) : Prop :=
  z % (c.modulus : ℤ) = c.residue % (c.modulus : ℤ)

instance (c : Congruence) (z : ℤ) : Decidable (c.Covers z) :=
  inferInstanceAs (Decidable (_ = _))

/-- A finite list covers every integer. -/
def CoversAll (cs : List Congruence) : Prop :=
  ∀ z : ℤ, ∃ c ∈ cs, c.Covers z

/-- No modulus appears twice, even with different residues. -/
def DistinctModuli (cs : List Congruence) : Prop :=
  (cs.map Congruence.modulus).Nodup

/-- The paper's definition of a finite distinct covering system. -/
def IsCoveringSystem (cs : List Congruence) : Prop :=
  CoversAll cs ∧ DistinctModuli cs ∧ ∀ c ∈ cs, 1 < c.modulus

/-- The minimum is attained, and is a lower bound for every modulus. -/
def HasSmallestModulus (cs : List Congruence) (n : ℕ) : Prop :=
  (∀ c ∈ cs, n ≤ c.modulus) ∧ ∃ c ∈ cs, c.modulus = n

/-- Precise proposition asserted in Nielsen's paper. -/
def MinimumModulus40 : Prop :=
  ∃ cs : List Congruence, IsCoveringSystem cs ∧ HasSmallestModulus cs 40

@[simp] theorem covers_zero_modulus (a z : ℤ) :
    (Congruence.mk 0 a).Covers z ↔ z = a := by
  simp [Congruence.Covers]

/-- Congruences are periodic with every multiple of their modulus. -/
theorem Congruence.covers_emod_iff (c : Congruence) (z : ℤ) (period : ℕ)
    (h : c.modulus ∣ period) :
    c.Covers (z % (period : ℤ)) ↔ c.Covers z := by
  obtain ⟨k, rfl⟩ := h
  simp [Congruence.Covers, Int.emod_emod_of_dvd]

/-- A finite common-period check suffices to cover all integers. -/
theorem coversAll_of_period (cs : List Congruence) (period : ℕ)
    (hp : 0 < period)
    (hdiv : ∀ c ∈ cs, c.modulus ∣ period)
    (hcover : ∀ r : Fin period, ∃ c ∈ cs, c.Covers (r.val : ℤ)) :
    CoversAll cs := by
  intro z
  have hpz : (0 : ℤ) < period := by exact_mod_cast hp
  have hnonneg : 0 ≤ z % (period : ℤ) := Int.emod_nonneg z (ne_of_gt hpz)
  have hlt : z % (period : ℤ) < period := Int.emod_lt_of_pos z hpz
  let r : Fin period := ⟨(z % (period : ℤ)).toNat, by omega⟩
  obtain ⟨c, hc, hcr⟩ := hcover r
  refine ⟨c, hc, ?_⟩
  have hr : (r.val : ℤ) = z % (period : ℤ) := by
    simp [r, Int.toNat_of_nonneg hnonneg]
  rw [hr] at hcr
  exact (c.covers_emod_iff z period (hdiv c hc)).mp hcr

/-- Increasing the list of classes preserves the covering property. -/
theorem CoversAll.mono {cs ds : List Congruence}
    (h : CoversAll cs) (hsub : ∀ c ∈ cs, c ∈ ds) : CoversAll ds := by
  intro z
  obtain ⟨c, hc, hz⟩ := h z
  exact ⟨c, hsub c hc, hz⟩

end Modulus40
