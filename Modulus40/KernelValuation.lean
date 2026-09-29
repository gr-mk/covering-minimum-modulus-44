import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Kernel-computable valuations

Mathlib's valuation implementations use well-founded recursion through opaque
proofs. A structurally recursive fuel bound permits ordinary kernel reduction
of the finite certificate tests. Its value is proved equal to `padicValNat`.
-/

namespace Modulus40

def valuationWithFuel (fuel p n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ recurse p n =>
      if 1 < p ∧ 0 < n ∧ n % p = 0 then recurse p (n / p) + 1 else 0) fuel p n

@[simp] theorem valuationWithFuel_succ (fuel p n : ℕ) :
    valuationWithFuel (fuel + 1) p n =
      if 1 < p ∧ 0 < n ∧ n % p = 0 then valuationWithFuel fuel p (n / p) + 1 else 0 := rfl

theorem maxPowDiv_step (p n : ℕ) :
    Nat.maxPowDiv p n =
      if 1 < p ∧ 0 < n ∧ n % p = 0 then Nat.maxPowDiv p (n / p) + 1 else 0 := by
  conv_lhs => rw [Nat.maxPowDiv, Nat.maxPowDiv.go]
  split_ifs
  · exact Nat.maxPowDiv.go_succ
  · rfl

theorem valuationWithFuel_eq_maxPowDiv (fuel p n : ℕ) (hbound : n ≤ fuel) :
    valuationWithFuel fuel p n = Nat.maxPowDiv p n := by
  induction fuel generalizing n with
  | zero =>
    have hn : n = 0 := by omega
    simp [hn, valuationWithFuel]
  | succ fuel ih =>
    rw [valuationWithFuel_succ, maxPowDiv_step]
    split_ifs with h
    · have hdiv : n / p < n := Nat.div_lt_self h.2.1 h.1
      rw [ih (n / p) (by omega)]
    · rfl

/-- A bound on the valuation itself is sufficient fuel. -/
theorem valuationWithFuel_eq_of_valuation_le (fuel p n : ℕ)
    (hbound : Nat.maxPowDiv p n ≤ fuel) :
    valuationWithFuel fuel p n = Nat.maxPowDiv p n := by
  induction fuel generalizing n with
  | zero =>
    have hzero : Nat.maxPowDiv p n = 0 := by omega
    simpa [valuationWithFuel] using hzero.symm
  | succ fuel ih =>
    rw [valuationWithFuel_succ, maxPowDiv_step]
    split_ifs with h
    · have hb : Nat.maxPowDiv p (n / p) ≤ fuel := by
        rw [maxPowDiv_step, if_pos h] at hbound
        omega
      rw [ih (n / p) hb]
    · rfl

/-- Every nontrivial prime-power divisor uses at least one binary digit per exponent. -/
theorem maxPowDiv_le_log2 (p n : ℕ) : Nat.maxPowDiv p n ≤ n.log2 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hp : 1 < p
  · apply (Nat.le_log2 hn).mpr
    calc
      2 ^ Nat.maxPowDiv p n ≤ p ^ Nat.maxPowDiv p n := Nat.pow_le_pow_left hp _
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.maxPowDiv.pow_dvd p n)
  · rw [maxPowDiv_step, if_neg (by tauto)]
    exact Nat.zero_le _

/-- Logarithmic fuel permits direct kernel computation without a large recursion cache. -/
def kernelPadicVal (p n : ℕ) : ℕ := valuationWithFuel n.log2 p n

theorem kernelPadicVal_eq_padicValNat (p n : ℕ) : kernelPadicVal p n = padicValNat p n := by
  rw [kernelPadicVal, valuationWithFuel_eq_of_valuation_le n.log2 p n (maxPowDiv_le_log2 p n),
    padicValNat.padicValNat_eq_maxPowDiv]

example : kernelPadicVal 2 8 = 3 := by decide
example : kernelPadicVal 3 0 = 0 := by decide
example : kernelPadicVal 107 11449 = 2 := by decide

end Modulus40
