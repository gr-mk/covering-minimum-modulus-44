import UC85.W.C.S3_21_107_t31.Tab
import UC85.W.C.S3_21_107_t31.I0
import UC85.W.C.S3_21_107_t31.S0
import UC85.W.C.S3_21_107_t31.S1
import UC85.W.C.S3_21_107_t31.S2
import UC85.W.C.S3_21_107_t31.S3
import UC85.W.C.S3_21_107_t31.S4
import UC85.W.C.S3_21_107_t31.S5
import UC85.W.C.S3_21_107_t31.S6
import UC85.W.C.S3_21_107_t31.S7
import UC85.W.C.S3_21_107_t31.S8
import UC85.W.C.S3_21_107_t31.S9
import UC85.W.C.S3_21_107_t31.S10
import UC85.W.C.S3_21_107_t31.S11
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_107_t31
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

theorem initUpTo_8 : ∀ i, i < 1152 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1024
  · exact initUpTo_7 i h
  have hk := oBlock8 (i - 1024) (by omega)
  rwa [show 1024 + (i - 1024) = i by omega] at hk

theorem initUpTo_9 : ∀ i, i < 1280 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1152
  · exact initUpTo_8 i h
  have hk := oBlock9 (i - 1152) (by omega)
  rwa [show 1152 + (i - 1152) = i by omega] at hk

theorem initUpTo_10 : ∀ i, i < 1408 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1280
  · exact initUpTo_9 i h
  have hk := oBlock10 (i - 1280) (by omega)
  rwa [show 1280 + (i - 1280) = i by omega] at hk

theorem initUpTo_11 : ∀ i, i < 1536 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1408
  · exact initUpTo_10 i h
  have hk := oBlock11 (i - 1408) (by omega)
  rwa [show 1408 + (i - 1408) = i by omega] at hk

theorem initUpTo_12 : ∀ i, i < 1664 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1536
  · exact initUpTo_11 i h
  have hk := oBlock12 (i - 1536) (by omega)
  rwa [show 1536 + (i - 1536) = i by omega] at hk

theorem initUpTo_13 : ∀ i, i < 1792 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1664
  · exact initUpTo_12 i h
  have hk := oBlock13 (i - 1664) (by omega)
  rwa [show 1664 + (i - 1664) = i by omega] at hk

theorem initUpTo_14 : ∀ i, i < 1855 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1792
  · exact initUpTo_13 i h
  have hk := oBlock14 (i - 1792) (by omega)
  rwa [show 1792 + (i - 1792) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 1855 ≤ i → i < 1983 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 1855) (by omega)
  rwa [show 1855 + (i - 1855) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 1855 ≤ i → i < 2111 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 1983
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 1983) (by omega)
  rwa [show 1983 + (i - 1983) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 1855 ≤ i → i < 2239 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2111
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 2111) (by omega)
  rwa [show 2111 + (i - 2111) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 1855 ≤ i → i < 2367 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2239
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 2239) (by omega)
  rwa [show 2239 + (i - 2239) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 1855 ≤ i → i < 2495 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2367
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 2367) (by omega)
  rwa [show 2367 + (i - 2367) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 1855 ≤ i → i < 2623 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2495
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 2495) (by omega)
  rwa [show 2495 + (i - 2495) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 1855 ≤ i → i < 2751 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2623
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 2623) (by omega)
  rwa [show 2623 + (i - 2623) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 1855 ≤ i → i < 2879 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2751
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 2751) (by omega)
  rwa [show 2751 + (i - 2751) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 1855 ≤ i → i < 3007 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2879
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 2879) (by omega)
  rwa [show 2879 + (i - 2879) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 1855 ≤ i → i < 3135 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3007
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 3007) (by omega)
  rwa [show 3007 + (i - 3007) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 1855 ≤ i → i < 3263 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3135
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 3135) (by omega)
  rwa [show 3135 + (i - 3135) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 1855 ≤ i → i < 3333 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3263
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 3263) (by omega)
  rwa [show 3263 + (i - 3263) = i by omega] at hk

/-- Check S3_21_107_t31: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 1855 3333 3332
    initUpTo_14 stepUpTo_11 (by decide) final_ok z hz

end UC85.W.C.S3_21_107_t31
