import UC85.W.C.S3_12_t15.Tab
import UC85.W.C.S3_12_t15.I0
import UC85.W.C.S3_12_t15.S0
import UC85.W.C.S3_12_t15.S1
import UC85.W.C.S3_12_t15.S2
import UC85.W.C.S3_12_t15.S3
import UC85.W.C.S3_12_t15.S4
import UC85.W.C.S3_12_t15.S5
import UC85.W.C.S3_12_t15.S6
import UC85.W.C.S3_12_t15.S7
import UC85.W.C.S3_12_t15.S8
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_12_t15
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

theorem initUpTo_7 : ∀ i, i < 961 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 896
  · exact initUpTo_6 i h
  have hk := oBlock7 (i - 896) (by omega)
  rwa [show 896 + (i - 896) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 961 ≤ i → i < 1089 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 961) (by omega)
  rwa [show 961 + (i - 961) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 961 ≤ i → i < 1217 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1089
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 1089) (by omega)
  rwa [show 1089 + (i - 1089) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 961 ≤ i → i < 1345 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1217
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 1217) (by omega)
  rwa [show 1217 + (i - 1217) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 961 ≤ i → i < 1473 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1345
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 1345) (by omega)
  rwa [show 1345 + (i - 1345) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 961 ≤ i → i < 1601 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1473
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 1473) (by omega)
  rwa [show 1473 + (i - 1473) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 961 ≤ i → i < 1729 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1601
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 1601) (by omega)
  rwa [show 1601 + (i - 1601) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 961 ≤ i → i < 1857 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1729
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 1729) (by omega)
  rwa [show 1729 + (i - 1729) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 961 ≤ i → i < 1985 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1857
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 1857) (by omega)
  rwa [show 1857 + (i - 1857) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 961 ≤ i → i < 2017 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1985
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 1985) (by omega)
  rwa [show 1985 + (i - 1985) = i by omega] at hk

/-- Check S3_12_t15: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 961 2017 2016
    initUpTo_7 stepUpTo_8 (by decide) final_ok z hz

end UC85.W.C.S3_12_t15
