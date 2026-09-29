import UC85.W.C.S3_14_t17.Tab
import UC85.W.C.S3_14_t17.I0
import UC85.W.C.S3_14_t17.I1
import UC85.W.C.S3_14_t17.I2
import UC85.W.C.S3_14_t17.S0
import UC85.W.C.S3_14_t17.S1
import UC85.W.C.S3_14_t17.S2
import UC85.W.C.S3_14_t17.S3
import UC85.W.C.S3_14_t17.S4
import UC85.W.C.S3_14_t17.S5
import UC85.W.C.S3_14_t17.S6
import UC85.W.C.S3_14_t17.S7
import UC85.W.C.S3_14_t17.S8
import UC85.W.C.S3_14_t17.S9
import UC85.W.C.S3_14_t17.S10
import UC85.W.C.S3_14_t17.S11
import UC85.W.C.S3_14_t17.S12
import UC85.W.C.S3_14_t17.S13
import UC85.W.C.S3_14_t17.S14
import UC85.W.C.S3_14_t17.S15
import UC85.W.C.S3_14_t17.S16
import UC85.W.C.S3_14_t17.S17
import UC85.W.C.S3_14_t17.S18
import UC85.W.C.S3_14_t17.S19
import UC85.W.C.S3_14_t17.S20
import UC85.W.C.S3_14_t17.S21
import UC85.W.C.S3_14_t17.S22
import UC85.W.C.S3_14_t17.S23
import UC85.W.C.S3_14_t17.S24
import UC85.W.C.S3_14_t17.S25
import UC85.W.C.S3_14_t17.S26
import UC85.W.C.S3_14_t17.S27
import UC85.W.C.S3_14_t17.S28
import UC85.W.C.S3_14_t17.S29
import UC85.W.C.S3_14_t17.S30
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_14_t17
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

theorem initUpTo_29 : ∀ i, i < 3840 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3712
  · exact initUpTo_28 i h
  have hk := oBlock29 (i - 3712) (by omega)
  rwa [show 3712 + (i - 3712) = i by omega] at hk

theorem initUpTo_30 : ∀ i, i < 3968 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3840
  · exact initUpTo_29 i h
  have hk := oBlock30 (i - 3840) (by omega)
  rwa [show 3840 + (i - 3840) = i by omega] at hk

theorem initUpTo_31 : ∀ i, i < 4096 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 3968
  · exact initUpTo_30 i h
  have hk := oBlock31 (i - 3968) (by omega)
  rwa [show 3968 + (i - 3968) = i by omega] at hk

theorem initUpTo_32 : ∀ i, i < 4224 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4096
  · exact initUpTo_31 i h
  have hk := oBlock32 (i - 4096) (by omega)
  rwa [show 4096 + (i - 4096) = i by omega] at hk

theorem initUpTo_33 : ∀ i, i < 4290 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4224
  · exact initUpTo_32 i h
  have hk := oBlock33 (i - 4224) (by omega)
  rwa [show 4224 + (i - 4224) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 4290 ≤ i → i < 4418 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 4290) (by omega)
  rwa [show 4290 + (i - 4290) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 4290 ≤ i → i < 4546 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4418
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 4418) (by omega)
  rwa [show 4418 + (i - 4418) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 4290 ≤ i → i < 4674 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4546
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 4546) (by omega)
  rwa [show 4546 + (i - 4546) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 4290 ≤ i → i < 4802 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4674
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 4674) (by omega)
  rwa [show 4674 + (i - 4674) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 4290 ≤ i → i < 4930 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4802
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 4802) (by omega)
  rwa [show 4802 + (i - 4802) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 4290 ≤ i → i < 5058 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 4930
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 4930) (by omega)
  rwa [show 4930 + (i - 4930) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 4290 ≤ i → i < 5186 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5058
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 5058) (by omega)
  rwa [show 5058 + (i - 5058) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 4290 ≤ i → i < 5314 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5186
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 5186) (by omega)
  rwa [show 5186 + (i - 5186) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 4290 ≤ i → i < 5442 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5314
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 5314) (by omega)
  rwa [show 5314 + (i - 5314) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 4290 ≤ i → i < 5570 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5442
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 5442) (by omega)
  rwa [show 5442 + (i - 5442) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 4290 ≤ i → i < 5698 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5570
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 5570) (by omega)
  rwa [show 5570 + (i - 5570) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 4290 ≤ i → i < 5826 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5698
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 5698) (by omega)
  rwa [show 5698 + (i - 5698) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 4290 ≤ i → i < 5954 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5826
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 5826) (by omega)
  rwa [show 5826 + (i - 5826) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 4290 ≤ i → i < 6082 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 5954
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 5954) (by omega)
  rwa [show 5954 + (i - 5954) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 4290 ≤ i → i < 6210 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6082
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 6082) (by omega)
  rwa [show 6082 + (i - 6082) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 4290 ≤ i → i < 6338 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6210
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 6210) (by omega)
  rwa [show 6210 + (i - 6210) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 4290 ≤ i → i < 6466 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6338
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 6338) (by omega)
  rwa [show 6338 + (i - 6338) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 4290 ≤ i → i < 6594 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6466
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 6466) (by omega)
  rwa [show 6466 + (i - 6466) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 4290 ≤ i → i < 6722 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6594
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 6594) (by omega)
  rwa [show 6594 + (i - 6594) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 4290 ≤ i → i < 6850 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6722
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 6722) (by omega)
  rwa [show 6722 + (i - 6722) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 4290 ≤ i → i < 6978 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6850
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 6850) (by omega)
  rwa [show 6850 + (i - 6850) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 4290 ≤ i → i < 7106 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6978
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 6978) (by omega)
  rwa [show 6978 + (i - 6978) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 4290 ≤ i → i < 7234 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7106
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 7106) (by omega)
  rwa [show 7106 + (i - 7106) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 4290 ≤ i → i < 7362 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7234
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 7234) (by omega)
  rwa [show 7234 + (i - 7234) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 4290 ≤ i → i < 7490 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7362
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 7362) (by omega)
  rwa [show 7362 + (i - 7362) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 4290 ≤ i → i < 7618 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7490
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 7490) (by omega)
  rwa [show 7490 + (i - 7490) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 4290 ≤ i → i < 7746 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7618
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 7618) (by omega)
  rwa [show 7618 + (i - 7618) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 4290 ≤ i → i < 7874 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7746
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 7746) (by omega)
  rwa [show 7746 + (i - 7746) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 4290 ≤ i → i < 8002 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7874
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 7874) (by omega)
  rwa [show 7874 + (i - 7874) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 4290 ≤ i → i < 8130 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8002
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 8002) (by omega)
  rwa [show 8002 + (i - 8002) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 4290 ≤ i → i < 8133 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8130
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 8130) (by omega)
  rwa [show 8130 + (i - 8130) = i by omega] at hk

/-- Check S3_14_t17: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 11868, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 4290 8133 8132
    initUpTo_33 stepUpTo_30 (by decide) final_ok z hz

end UC85.W.C.S3_14_t17
