import UC85.W.C.S3_11_t13.Tab
import UC85.W.C.S3_11_t13.I0
import UC85.W.C.S3_11_t13.S0
import UC85.W.C.S3_11_t13.S1
import UC85.W.C.S3_11_t13.S2
import UC85.W.C.S3_11_t13.S3
import UC85.W.C.S3_11_t13.S4
import UC85.W.C.S3_11_t13.S5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_11_t13
open Modulus40 UC85.W.U

theorem initUpTo_0 : ∀ i, i < 128 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  have hk := oBlock0 (i - 0) (by omega)
  rwa [show 0 + (i - 0) = i by omega] at hk

theorem initUpTo_1 : ∀ i, i < 256 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 128
  · exact initUpTo_0 i h
  have hk := oBlock1 (i - 128) (by omega)
  rwa [show 128 + (i - 128) = i by omega] at hk

theorem initUpTo_2 : ∀ i, i < 384 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 256
  · exact initUpTo_1 i h
  have hk := oBlock2 (i - 256) (by omega)
  rwa [show 256 + (i - 256) = i by omega] at hk

theorem initUpTo_3 : ∀ i, i < 512 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 384
  · exact initUpTo_2 i h
  have hk := oBlock3 (i - 384) (by omega)
  rwa [show 384 + (i - 384) = i by omega] at hk

theorem initUpTo_4 : ∀ i, i < 640 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 512
  · exact initUpTo_3 i h
  have hk := oBlock4 (i - 512) (by omega)
  rwa [show 512 + (i - 512) = i by omega] at hk

theorem initUpTo_5 : ∀ i, i < 768 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 640
  · exact initUpTo_4 i h
  have hk := oBlock5 (i - 640) (by omega)
  rwa [show 640 + (i - 640) = i by omega] at hk

theorem initUpTo_6 : ∀ i, i < 896 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 768
  · exact initUpTo_5 i h
  have hk := oBlock6 (i - 768) (by omega)
  rwa [show 768 + (i - 768) = i by omega] at hk

theorem initUpTo_7 : ∀ i, i < 1024 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 896
  · exact initUpTo_6 i h
  have hk := oBlock7 (i - 896) (by omega)
  rwa [show 896 + (i - 896) = i by omega] at hk

theorem initUpTo_8 : ∀ i, i < 1056 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1024
  · exact initUpTo_7 i h
  have hk := oBlock8 (i - 1024) (by omega)
  rwa [show 1024 + (i - 1024) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 1056 ≤ i → i < 1184 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 1056) (by omega)
  rwa [show 1056 + (i - 1056) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 1056 ≤ i → i < 1312 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1184
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 1184) (by omega)
  rwa [show 1184 + (i - 1184) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 1056 ≤ i → i < 1440 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1312
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 1312) (by omega)
  rwa [show 1312 + (i - 1312) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 1056 ≤ i → i < 1568 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1440
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 1440) (by omega)
  rwa [show 1440 + (i - 1440) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 1056 ≤ i → i < 1696 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1568
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 1568) (by omega)
  rwa [show 1568 + (i - 1568) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 1056 ≤ i → i < 1757 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1696
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 1696) (by omega)
  rwa [show 1696 + (i - 1696) = i by omega] at hk

/-- Check S3_11_t13: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 3312, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 1056 1757 1756
    initUpTo_8 stepUpTo_5 (by decide) final_ok z hz

end UC85.W.C.S3_11_t13
