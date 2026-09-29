import UC85.W.C.S3_21_151_t39.Tab
import UC85.W.C.S3_21_151_t39.I0
import UC85.W.C.S3_21_151_t39.I1
import UC85.W.C.S3_21_151_t39.S0
import UC85.W.C.S3_21_151_t39.S1
import UC85.W.C.S3_21_151_t39.S2
import UC85.W.C.S3_21_151_t39.S3
import UC85.W.C.S3_21_151_t39.S4
import UC85.W.C.S3_21_151_t39.S5
import UC85.W.C.S3_21_151_t39.S6
import UC85.W.C.S3_21_151_t39.S7
import UC85.W.C.S3_21_151_t39.S8
import UC85.W.C.S3_21_151_t39.S9
import UC85.W.C.S3_21_151_t39.S10
import UC85.W.C.S3_21_151_t39.S11
import UC85.W.C.S3_21_151_t39.S12
import UC85.W.C.S3_21_151_t39.S13
import UC85.W.C.S3_21_151_t39.S14
import UC85.W.C.S3_21_151_t39.S15
import UC85.W.C.S3_21_151_t39.S16
import UC85.W.C.S3_21_151_t39.S17
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_151_t39
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

theorem initUpTo_14 : ∀ i, i < 1920 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1792
  · exact initUpTo_13 i h
  have hk := oBlock14 (i - 1792) (by omega)
  rwa [show 1792 + (i - 1792) = i by omega] at hk

theorem initUpTo_15 : ∀ i, i < 2048 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 1920
  · exact initUpTo_14 i h
  have hk := oBlock15 (i - 1920) (by omega)
  rwa [show 1920 + (i - 1920) = i by omega] at hk

theorem initUpTo_16 : ∀ i, i < 2176 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2048
  · exact initUpTo_15 i h
  have hk := oBlock16 (i - 2048) (by omega)
  rwa [show 2048 + (i - 2048) = i by omega] at hk

theorem initUpTo_17 : ∀ i, i < 2304 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2176
  · exact initUpTo_16 i h
  have hk := oBlock17 (i - 2176) (by omega)
  rwa [show 2176 + (i - 2176) = i by omega] at hk

theorem initUpTo_18 : ∀ i, i < 2432 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2304
  · exact initUpTo_17 i h
  have hk := oBlock18 (i - 2304) (by omega)
  rwa [show 2304 + (i - 2304) = i by omega] at hk

theorem initUpTo_19 : ∀ i, i < 2560 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2432
  · exact initUpTo_18 i h
  have hk := oBlock19 (i - 2432) (by omega)
  rwa [show 2432 + (i - 2432) = i by omega] at hk

theorem initUpTo_20 : ∀ i, i < 2688 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2560
  · exact initUpTo_19 i h
  have hk := oBlock20 (i - 2560) (by omega)
  rwa [show 2560 + (i - 2560) = i by omega] at hk

theorem initUpTo_21 : ∀ i, i < 2816 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2688
  · exact initUpTo_20 i h
  have hk := oBlock21 (i - 2688) (by omega)
  rwa [show 2688 + (i - 2688) = i by omega] at hk

theorem initUpTo_22 : ∀ i, i < 2944 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2816
  · exact initUpTo_21 i h
  have hk := oBlock22 (i - 2816) (by omega)
  rwa [show 2816 + (i - 2816) = i by omega] at hk

theorem initUpTo_23 : ∀ i, i < 3072 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2944
  · exact initUpTo_22 i h
  have hk := oBlock23 (i - 2944) (by omega)
  rwa [show 2944 + (i - 2944) = i by omega] at hk

theorem initUpTo_24 : ∀ i, i < 3200 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3072
  · exact initUpTo_23 i h
  have hk := oBlock24 (i - 3072) (by omega)
  rwa [show 3072 + (i - 3072) = i by omega] at hk

theorem initUpTo_25 : ∀ i, i < 3328 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3200
  · exact initUpTo_24 i h
  have hk := oBlock25 (i - 3200) (by omega)
  rwa [show 3200 + (i - 3200) = i by omega] at hk

theorem initUpTo_26 : ∀ i, i < 3456 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3328
  · exact initUpTo_25 i h
  have hk := oBlock26 (i - 3328) (by omega)
  rwa [show 3328 + (i - 3328) = i by omega] at hk

theorem initUpTo_27 : ∀ i, i < 3584 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3456
  · exact initUpTo_26 i h
  have hk := oBlock27 (i - 3456) (by omega)
  rwa [show 3456 + (i - 3456) = i by omega] at hk

theorem initUpTo_28 : ∀ i, i < 3641 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3584
  · exact initUpTo_27 i h
  have hk := oBlock28 (i - 3584) (by omega)
  rwa [show 3584 + (i - 3584) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 3641 ≤ i → i < 3769 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 3641) (by omega)
  rwa [show 3641 + (i - 3641) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 3641 ≤ i → i < 3897 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3769
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 3769) (by omega)
  rwa [show 3769 + (i - 3769) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 3641 ≤ i → i < 4025 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3897
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 3897) (by omega)
  rwa [show 3897 + (i - 3897) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 3641 ≤ i → i < 4153 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4025
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 4025) (by omega)
  rwa [show 4025 + (i - 4025) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 3641 ≤ i → i < 4281 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4153
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 4153) (by omega)
  rwa [show 4153 + (i - 4153) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 3641 ≤ i → i < 4409 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4281
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 4281) (by omega)
  rwa [show 4281 + (i - 4281) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 3641 ≤ i → i < 4537 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4409
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 4409) (by omega)
  rwa [show 4409 + (i - 4409) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 3641 ≤ i → i < 4665 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4537
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 4537) (by omega)
  rwa [show 4537 + (i - 4537) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 3641 ≤ i → i < 4793 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4665
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 4665) (by omega)
  rwa [show 4665 + (i - 4665) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 3641 ≤ i → i < 4921 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4793
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 4793) (by omega)
  rwa [show 4793 + (i - 4793) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 3641 ≤ i → i < 5049 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4921
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 4921) (by omega)
  rwa [show 4921 + (i - 4921) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 3641 ≤ i → i < 5177 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5049
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 5049) (by omega)
  rwa [show 5049 + (i - 5049) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 3641 ≤ i → i < 5305 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5177
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 5177) (by omega)
  rwa [show 5177 + (i - 5177) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 3641 ≤ i → i < 5433 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5305
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 5305) (by omega)
  rwa [show 5305 + (i - 5305) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 3641 ≤ i → i < 5561 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5433
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 5433) (by omega)
  rwa [show 5433 + (i - 5433) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 3641 ≤ i → i < 5689 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5561
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 5561) (by omega)
  rwa [show 5561 + (i - 5561) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 3641 ≤ i → i < 5817 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5689
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 5689) (by omega)
  rwa [show 5689 + (i - 5689) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 3641 ≤ i → i < 5832 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5817
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 5817) (by omega)
  rwa [show 5817 + (i - 5817) = i by omega] at hk

/-- Check S3_21_151_t39: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 3641 5832 5831
    initUpTo_28 stepUpTo_17 (by decide) final_ok z hz

end UC85.W.C.S3_21_151_t39
