import UC85.W.C.S3_21_149_t38.Tab
import UC85.W.C.S3_21_149_t38.I0
import UC85.W.C.S3_21_149_t38.I1
import UC85.W.C.S3_21_149_t38.S0
import UC85.W.C.S3_21_149_t38.S1
import UC85.W.C.S3_21_149_t38.S2
import UC85.W.C.S3_21_149_t38.S3
import UC85.W.C.S3_21_149_t38.S4
import UC85.W.C.S3_21_149_t38.S5
import UC85.W.C.S3_21_149_t38.S6
import UC85.W.C.S3_21_149_t38.S7
import UC85.W.C.S3_21_149_t38.S8
import UC85.W.C.S3_21_149_t38.S9
import UC85.W.C.S3_21_149_t38.S10
import UC85.W.C.S3_21_149_t38.S11
import UC85.W.C.S3_21_149_t38.S12
import UC85.W.C.S3_21_149_t38.S13
import UC85.W.C.S3_21_149_t38.S14
import UC85.W.C.S3_21_149_t38.S15
import UC85.W.C.S3_21_149_t38.S16
import UC85.W.C.S3_21_149_t38.S17
import UC85.W.C.S3_21_149_t38.S18
import UC85.W.C.S3_21_149_t38.S19
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_149_t38
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

theorem initUpTo_21 : ∀ i, i < 2729 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 2688
  · exact initUpTo_20 i h
  have hk := oBlock21 (i - 2688) (by omega)
  rwa [show 2688 + (i - 2688) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 2729 ≤ i → i < 2857 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 2729) (by omega)
  rwa [show 2729 + (i - 2729) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 2729 ≤ i → i < 2985 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2857
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 2857) (by omega)
  rwa [show 2857 + (i - 2857) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 2729 ≤ i → i < 3113 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 2985
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 2985) (by omega)
  rwa [show 2985 + (i - 2985) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 2729 ≤ i → i < 3241 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3113
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 3113) (by omega)
  rwa [show 3113 + (i - 3113) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 2729 ≤ i → i < 3369 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3241
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 3241) (by omega)
  rwa [show 3241 + (i - 3241) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 2729 ≤ i → i < 3497 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3369
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 3369) (by omega)
  rwa [show 3369 + (i - 3369) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 2729 ≤ i → i < 3625 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3497
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 3497) (by omega)
  rwa [show 3497 + (i - 3497) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 2729 ≤ i → i < 3753 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3625
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 3625) (by omega)
  rwa [show 3625 + (i - 3625) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 2729 ≤ i → i < 3881 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3753
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 3753) (by omega)
  rwa [show 3753 + (i - 3753) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 2729 ≤ i → i < 4009 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3881
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 3881) (by omega)
  rwa [show 3881 + (i - 3881) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 2729 ≤ i → i < 4137 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4009
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 4009) (by omega)
  rwa [show 4009 + (i - 4009) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 2729 ≤ i → i < 4265 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4137
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 4137) (by omega)
  rwa [show 4137 + (i - 4137) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 2729 ≤ i → i < 4393 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4265
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 4265) (by omega)
  rwa [show 4265 + (i - 4265) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 2729 ≤ i → i < 4521 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4393
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 4393) (by omega)
  rwa [show 4393 + (i - 4393) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 2729 ≤ i → i < 4649 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4521
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 4521) (by omega)
  rwa [show 4521 + (i - 4521) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 2729 ≤ i → i < 4777 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4649
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 4649) (by omega)
  rwa [show 4649 + (i - 4649) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 2729 ≤ i → i < 4905 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4777
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 4777) (by omega)
  rwa [show 4777 + (i - 4777) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 2729 ≤ i → i < 5033 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4905
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 4905) (by omega)
  rwa [show 4905 + (i - 4905) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 2729 ≤ i → i < 5161 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5033
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 5033) (by omega)
  rwa [show 5033 + (i - 5033) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 2729 ≤ i → i < 5193 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5161
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 5161) (by omega)
  rwa [show 5161 + (i - 5161) = i by omega] at hk

/-- Check S3_21_149_t38: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 2729 5193 5192
    initUpTo_21 stepUpTo_19 (by decide) final_ok z hz

end UC85.W.C.S3_21_149_t38
