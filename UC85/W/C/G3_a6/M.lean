import UC85.W.C.G3_a6.Tab
import UC85.W.C.G3_a6.I0
import UC85.W.C.G3_a6.S0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.G3_a6
open Modulus40 UC85.W.U

theorem initUpTo_0 : ∀ i, i < 1 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  have hk := oBlock0 (i - 0) (by omega)
  rwa [show 0 + (i - 0) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 1 ≤ i → i < 2 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 1) (by omega)
  rwa [show 1 + (i - 1) = i by omega] at hk

/-- Check G3_a6: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 47, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 1 2 1
    initUpTo_0 stepUpTo_0 (by decide) final_ok z hz

end UC85.W.C.G3_a6
