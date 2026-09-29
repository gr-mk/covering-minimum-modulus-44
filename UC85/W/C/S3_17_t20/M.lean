import UC85.W.C.S3_17_t20.Tab
import UC85.W.C.S3_17_t20.I0
import UC85.W.C.S3_17_t20.I1
import UC85.W.C.S3_17_t20.S0
import UC85.W.C.S3_17_t20.S1
import UC85.W.C.S3_17_t20.S2
import UC85.W.C.S3_17_t20.S3
import UC85.W.C.S3_17_t20.S4
import UC85.W.C.S3_17_t20.S5
import UC85.W.C.S3_17_t20.S6
import UC85.W.C.S3_17_t20.S7
import UC85.W.C.S3_17_t20.S8
import UC85.W.C.S3_17_t20.S9
import UC85.W.C.S3_17_t20.S10
import UC85.W.C.S3_17_t20.S11
import UC85.W.C.S3_17_t20.S12
import UC85.W.C.S3_17_t20.S13
import UC85.W.C.S3_17_t20.S14
import UC85.W.C.S3_17_t20.S15
import UC85.W.C.S3_17_t20.S16
import UC85.W.C.S3_17_t20.S17
import UC85.W.C.S3_17_t20.S18
import UC85.W.C.S3_17_t20.S19
import UC85.W.C.S3_17_t20.S20
import UC85.W.C.S3_17_t20.S21
import UC85.W.C.S3_17_t20.S22
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_17_t20
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

theorem initUpTo_28 : ∀ i, i < 3712 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3584
  · exact initUpTo_27 i h
  have hk := oBlock28 (i - 3584) (by omega)
  rwa [show 3584 + (i - 3584) = i by omega] at hk

theorem initUpTo_29 : ∀ i, i < 3830 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3712
  · exact initUpTo_28 i h
  have hk := oBlock29 (i - 3712) (by omega)
  rwa [show 3712 + (i - 3712) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 3830 ≤ i → i < 3958 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 3830) (by omega)
  rwa [show 3830 + (i - 3830) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 3830 ≤ i → i < 4086 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 3958
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 3958) (by omega)
  rwa [show 3958 + (i - 3958) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 3830 ≤ i → i < 4214 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4086
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 4086) (by omega)
  rwa [show 4086 + (i - 4086) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 3830 ≤ i → i < 4342 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4214
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 4214) (by omega)
  rwa [show 4214 + (i - 4214) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 3830 ≤ i → i < 4470 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4342
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 4342) (by omega)
  rwa [show 4342 + (i - 4342) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 3830 ≤ i → i < 4598 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4470
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 4470) (by omega)
  rwa [show 4470 + (i - 4470) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 3830 ≤ i → i < 4726 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4598
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 4598) (by omega)
  rwa [show 4598 + (i - 4598) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 3830 ≤ i → i < 4854 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4726
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 4726) (by omega)
  rwa [show 4726 + (i - 4726) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 3830 ≤ i → i < 4982 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4854
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 4854) (by omega)
  rwa [show 4854 + (i - 4854) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 3830 ≤ i → i < 5110 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4982
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 4982) (by omega)
  rwa [show 4982 + (i - 4982) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 3830 ≤ i → i < 5238 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5110
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 5110) (by omega)
  rwa [show 5110 + (i - 5110) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 3830 ≤ i → i < 5366 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5238
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 5238) (by omega)
  rwa [show 5238 + (i - 5238) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 3830 ≤ i → i < 5494 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5366
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 5366) (by omega)
  rwa [show 5366 + (i - 5366) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 3830 ≤ i → i < 5622 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5494
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 5494) (by omega)
  rwa [show 5494 + (i - 5494) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 3830 ≤ i → i < 5750 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5622
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 5622) (by omega)
  rwa [show 5622 + (i - 5622) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 3830 ≤ i → i < 5878 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5750
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 5750) (by omega)
  rwa [show 5750 + (i - 5750) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 3830 ≤ i → i < 6006 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5878
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 5878) (by omega)
  rwa [show 5878 + (i - 5878) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 3830 ≤ i → i < 6134 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6006
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 6006) (by omega)
  rwa [show 6006 + (i - 6006) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 3830 ≤ i → i < 6262 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6134
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 6134) (by omega)
  rwa [show 6134 + (i - 6134) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 3830 ≤ i → i < 6390 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6262
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 6262) (by omega)
  rwa [show 6262 + (i - 6262) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 3830 ≤ i → i < 6518 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6390
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 6390) (by omega)
  rwa [show 6390 + (i - 6390) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 3830 ≤ i → i < 6646 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6518
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 6518) (by omega)
  rwa [show 6518 + (i - 6518) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 3830 ≤ i → i < 6677 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6646
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 6646) (by omega)
  rwa [show 6646 + (i - 6646) = i by omega] at hk

/-- Check S3_17_t20: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 33136, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 3830 6677 6676
    initUpTo_29 stepUpTo_22 (by decide) final_ok z hz

end UC85.W.C.S3_17_t20
