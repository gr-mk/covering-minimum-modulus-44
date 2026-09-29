import UC85.W.U.GlueMain
import UC85.W.U.BoxMain
import UC85.W.U.MinMain
import UC85.ReductionN
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85
open Modulus40

theorem uc44_primes_prime : ∀ i, (UC85.W.U.primes i).Prime := by decide
theorem uc44_primes_inj : Function.Injective UC85.W.U.primes :=
  (Fin.strictMono_iff_lt_succ.2 (by decide)).injective
theorem uc44_fresh : ∀ i, ¬ 223 ∣ UC85.W.U.primes i := by decide

/-- The system of `UC85.W.U`, completed by gr-mk's truncation and fresh-prime caps (P = 223):
a finite covering system of the integers with distinct moduli and least modulus 44. -/
theorem minimumModulus44 : MinimumModulusN 44 :=
  minimumModulusN_of_symbolic (by norm_num) (by norm_num) (by decide : Nat.Prime 223) UC85.W.U.primes uc44_primes_prime uc44_primes_inj
    uc44_fresh UC85.W.U.patterns UC85.W.U.hsep UC85.W.U.hmin ⟨89, by decide⟩ UC85.W.U.wexp UC85.W.U.hw UC85.W.U.hwmod UC85.W.U.hcover_all

/-- An expanded form of the main theorem, with the required properties visible. -/
theorem exists_distinct_covering_minimum44 :
    ∃ classes : List Congruence,
      (∀ z : ℤ, ∃ c ∈ classes, z % (c.modulus : ℤ) = c.residue % (c.modulus : ℤ)) ∧
      (classes.map Congruence.modulus).Nodup ∧
      (∀ c ∈ classes, 44 ≤ c.modulus) ∧
      ∃ c ∈ classes, c.modulus = 44 := by
  obtain ⟨classes, hcover, hminimum⟩ := minimumModulus44
  exact ⟨classes, hcover.1, hcover.2.1, hminimum.1, hminimum.2⟩

end UC85
