import Modulus40.MainReduction
import Modulus40.LocalQuotientComplete
import Modulus40.KernelValuation

/-!
# From finite local signatures to the symbolic covering theorem

The arithmetic test for a ray uses its unique valuation level. All computations
used in certificate checks therefore have a proved relation to integer
congruences. A finite rectangle-cover proof can then select a single pattern
which works simultaneously in every prime coordinate.
-/

namespace Modulus40

/-- Conditions required for a ray to have its stated prime-power semantics. -/
def Coordinate.WellFormed (p : ℕ) : Coordinate → Prop
  | .fixed _ _ => True
  | .ray first _ digit => 1 ≤ first ∧ 1 ≤ digit ∧ digit < p

instance (p : ℕ) (s : Coordinate) : Decidable (s.WellFormed p) := by
  cases s <;> simp only [Coordinate.WellFormed] <;> infer_instance

/-- A computable test, whose correctness is proved below. -/
def Coordinate.test (s : Coordinate) (p : ℕ) (z : ℤ) : Bool :=
  match s with
  | .fixed exponent residue => decide ((Congruence.mk (p ^ exponent) residue).Covers z)
  | .ray first center digit =>
    let e := kernelPadicVal p (z - center).natAbs + 1
    decide (first ≤ e ∧ ((Coordinate.ray first center digit).at p e).Covers z)

/-- A successful finite test means actual membership in the symbolic family. -/
theorem Coordinate.test_eq_true_iff {p : ℕ} (hp : p.Prime) (s : Coordinate)
    (hs : s.WellFormed p) (z : ℤ) : s.test p z = true ↔ s.Matches p z := by
  cases s with
  | fixed exponent residue => simp [Coordinate.test]
  | ray first center digit =>
    rcases hs with ⟨hf, hd, hdq⟩
    rw [Coordinate.matches_ray]
    simp only [Coordinate.test, decide_eq_true_eq]
    simpa only [padicValInt, ← kernelPadicVal_eq_padicValNat] using
      (Ray.matches_iff_at_padicVal (r := Ray.mk p first center digit) hp hf hd hdq z).symm

/-- A collection of chosen finite local representatives suffices once their
signatures have been verified and their rectangle cover has been certified. -/
theorem symbolic_of_finite_signatures {d k : ℕ}
    (primes : Fin d → ℕ) (hprime : ∀ j, (primes j).Prime)
    (patterns : Fin k → PrimePattern d)
    (hgood : ∀ i j, (patterns i j).WellFormed (primes j))
    (arities : Fin d → ℕ) (representatives : (j : Fin d) → Fin (arities j) → ℤ)
    (hlocal : ∀ z : ℤ, (∀ i j, ¬ (patterns i j).IsRayCenter z) →
      ∀ j, ∃ a : Fin (arities j), ∀ i,
        (patterns i j).Matches (primes j) z ↔
          (patterns i j).Matches (primes j) (representatives j a))
    (hcover : ∀ assignment : (j : Fin d) → Fin (arities j), ∃ i, ∀ j,
      (patterns i j).test (primes j) (representatives j (assignment j)) = true) :
    ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z := by
  classical
  intro z
  by_cases hc : ∃ i j, (patterns i j).IsRayCenter z
  · exact Or.inr hc
  · left
    have hz : ∀ i j, ¬ (patterns i j).IsRayCenter z := by
      intro i j hij
      exact hc ⟨i, j, hij⟩
    choose assignment ha using hlocal z hz
    obtain ⟨i, hi⟩ := hcover assignment
    refine ⟨i, fun j => ?_⟩
    apply (ha j i).mpr
    exact (Coordinate.test_eq_true_iff (hprime j) (patterns i j)
      (hgood i j) _).mp (hi j)

end Modulus40
