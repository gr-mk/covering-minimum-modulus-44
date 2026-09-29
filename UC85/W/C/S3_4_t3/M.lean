import UC85.W.C.S3_4_t3.Tab
import UC85.W.C.S3_4_t3.I0
import UC85.W.C.S3_4_t3.S0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t3
open Modulus40 UC85.W.U

theorem initUpTo_0 : ∀ i, i < 101 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  have hk := oBlock0 (i - 0) (by omega)
  rwa [show 0 + (i - 0) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 101 ≤ i → i < 105 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 101) (by omega)
  rwa [show 101 + (i - 101) = i by omega] at hk

/-- Check S3_4_t3: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618422, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 101 105 104
    initUpTo_0 stepUpTo_0 (by decide) final_ok z hz

end UC85.W.C.S3_4_t3
