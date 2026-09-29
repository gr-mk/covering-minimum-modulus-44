import UC85.W.C.S3_21_193_t47.Tab
import UC85.W.C.S3_21_193_t47.I0
import UC85.W.C.S3_21_193_t47.I1
import UC85.W.C.S3_21_193_t47.I2
import UC85.W.C.S3_21_193_t47.I3
import UC85.W.C.S3_21_193_t47.S0
import UC85.W.C.S3_21_193_t47.S1
import UC85.W.C.S3_21_193_t47.S2
import UC85.W.C.S3_21_193_t47.S3
import UC85.W.C.S3_21_193_t47.S4
import UC85.W.C.S3_21_193_t47.S5
import UC85.W.C.S3_21_193_t47.S6
import UC85.W.C.S3_21_193_t47.S7
import UC85.W.C.S3_21_193_t47.S8
import UC85.W.C.S3_21_193_t47.S9
import UC85.W.C.S3_21_193_t47.S10
import UC85.W.C.S3_21_193_t47.S11
import UC85.W.C.S3_21_193_t47.S12
import UC85.W.C.S3_21_193_t47.S13
import UC85.W.C.S3_21_193_t47.S14
import UC85.W.C.S3_21_193_t47.S15
import UC85.W.C.S3_21_193_t47.S16
import UC85.W.C.S3_21_193_t47.S17
import UC85.W.C.S3_21_193_t47.S18
import UC85.W.C.S3_21_193_t47.S19
import UC85.W.C.S3_21_193_t47.S20
import UC85.W.C.S3_21_193_t47.S21
import UC85.W.C.S3_21_193_t47.S22
import UC85.W.C.S3_21_193_t47.S23
import UC85.W.C.S3_21_193_t47.S24
import UC85.W.C.S3_21_193_t47.S25
import UC85.W.C.S3_21_193_t47.S26
import UC85.W.C.S3_21_193_t47.S27
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_193_t47
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

theorem initUpTo_33 : ∀ i, i < 4352 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4224
  · exact initUpTo_32 i h
  have hk := oBlock33 (i - 4224) (by omega)
  rwa [show 4224 + (i - 4224) = i by omega] at hk

theorem initUpTo_34 : ∀ i, i < 4480 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4352
  · exact initUpTo_33 i h
  have hk := oBlock34 (i - 4352) (by omega)
  rwa [show 4352 + (i - 4352) = i by omega] at hk

theorem initUpTo_35 : ∀ i, i < 4608 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4480
  · exact initUpTo_34 i h
  have hk := oBlock35 (i - 4480) (by omega)
  rwa [show 4480 + (i - 4480) = i by omega] at hk

theorem initUpTo_36 : ∀ i, i < 4736 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4608
  · exact initUpTo_35 i h
  have hk := oBlock36 (i - 4608) (by omega)
  rwa [show 4608 + (i - 4608) = i by omega] at hk

theorem initUpTo_37 : ∀ i, i < 4864 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4736
  · exact initUpTo_36 i h
  have hk := oBlock37 (i - 4736) (by omega)
  rwa [show 4736 + (i - 4736) = i by omega] at hk

theorem initUpTo_38 : ∀ i, i < 4992 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4864
  · exact initUpTo_37 i h
  have hk := oBlock38 (i - 4864) (by omega)
  rwa [show 4864 + (i - 4864) = i by omega] at hk

theorem initUpTo_39 : ∀ i, i < 5120 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 4992
  · exact initUpTo_38 i h
  have hk := oBlock39 (i - 4992) (by omega)
  rwa [show 4992 + (i - 4992) = i by omega] at hk

theorem initUpTo_40 : ∀ i, i < 5248 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5120
  · exact initUpTo_39 i h
  have hk := oBlock40 (i - 5120) (by omega)
  rwa [show 5120 + (i - 5120) = i by omega] at hk

theorem initUpTo_41 : ∀ i, i < 5376 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5248
  · exact initUpTo_40 i h
  have hk := oBlock41 (i - 5248) (by omega)
  rwa [show 5248 + (i - 5248) = i by omega] at hk

theorem initUpTo_42 : ∀ i, i < 5504 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5376
  · exact initUpTo_41 i h
  have hk := oBlock42 (i - 5376) (by omega)
  rwa [show 5376 + (i - 5376) = i by omega] at hk

theorem initUpTo_43 : ∀ i, i < 5632 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5504
  · exact initUpTo_42 i h
  have hk := oBlock43 (i - 5504) (by omega)
  rwa [show 5504 + (i - 5504) = i by omega] at hk

theorem initUpTo_44 : ∀ i, i < 5760 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5632
  · exact initUpTo_43 i h
  have hk := oBlock44 (i - 5632) (by omega)
  rwa [show 5632 + (i - 5632) = i by omega] at hk

theorem initUpTo_45 : ∀ i, i < 5888 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5760
  · exact initUpTo_44 i h
  have hk := oBlock45 (i - 5760) (by omega)
  rwa [show 5760 + (i - 5760) = i by omega] at hk

theorem initUpTo_46 : ∀ i, i < 6016 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 5888
  · exact initUpTo_45 i h
  have hk := oBlock46 (i - 5888) (by omega)
  rwa [show 5888 + (i - 5888) = i by omega] at hk

theorem initUpTo_47 : ∀ i, i < 6144 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6016
  · exact initUpTo_46 i h
  have hk := oBlock47 (i - 6016) (by omega)
  rwa [show 6016 + (i - 6016) = i by omega] at hk

theorem initUpTo_48 : ∀ i, i < 6272 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6144
  · exact initUpTo_47 i h
  have hk := oBlock48 (i - 6144) (by omega)
  rwa [show 6144 + (i - 6144) = i by omega] at hk

theorem initUpTo_49 : ∀ i, i < 6318 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6272
  · exact initUpTo_48 i h
  have hk := oBlock49 (i - 6272) (by omega)
  rwa [show 6272 + (i - 6272) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 6318 ≤ i → i < 6446 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 6318) (by omega)
  rwa [show 6318 + (i - 6318) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 6318 ≤ i → i < 6574 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6446
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 6446) (by omega)
  rwa [show 6446 + (i - 6446) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 6318 ≤ i → i < 6702 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6574
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 6574) (by omega)
  rwa [show 6574 + (i - 6574) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 6318 ≤ i → i < 6830 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6702
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 6702) (by omega)
  rwa [show 6702 + (i - 6702) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 6318 ≤ i → i < 6958 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6830
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 6830) (by omega)
  rwa [show 6830 + (i - 6830) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 6318 ≤ i → i < 7086 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 6958
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 6958) (by omega)
  rwa [show 6958 + (i - 6958) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 6318 ≤ i → i < 7214 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7086
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 7086) (by omega)
  rwa [show 7086 + (i - 7086) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 6318 ≤ i → i < 7342 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7214
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 7214) (by omega)
  rwa [show 7214 + (i - 7214) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 6318 ≤ i → i < 7470 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7342
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 7342) (by omega)
  rwa [show 7342 + (i - 7342) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 6318 ≤ i → i < 7598 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7470
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 7470) (by omega)
  rwa [show 7470 + (i - 7470) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 6318 ≤ i → i < 7726 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7598
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 7598) (by omega)
  rwa [show 7598 + (i - 7598) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 6318 ≤ i → i < 7854 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7726
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 7726) (by omega)
  rwa [show 7726 + (i - 7726) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 6318 ≤ i → i < 7982 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7854
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 7854) (by omega)
  rwa [show 7854 + (i - 7854) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 6318 ≤ i → i < 8110 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 7982
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 7982) (by omega)
  rwa [show 7982 + (i - 7982) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 6318 ≤ i → i < 8238 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8110
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 8110) (by omega)
  rwa [show 8110 + (i - 8110) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 6318 ≤ i → i < 8366 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8238
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 8238) (by omega)
  rwa [show 8238 + (i - 8238) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 6318 ≤ i → i < 8494 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8366
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 8366) (by omega)
  rwa [show 8366 + (i - 8366) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 6318 ≤ i → i < 8622 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8494
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 8494) (by omega)
  rwa [show 8494 + (i - 8494) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 6318 ≤ i → i < 8750 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8622
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 8622) (by omega)
  rwa [show 8622 + (i - 8622) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 6318 ≤ i → i < 8878 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8750
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 8750) (by omega)
  rwa [show 8750 + (i - 8750) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 6318 ≤ i → i < 9006 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8878
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 8878) (by omega)
  rwa [show 8878 + (i - 8878) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 6318 ≤ i → i < 9134 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9006
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 9006) (by omega)
  rwa [show 9006 + (i - 9006) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 6318 ≤ i → i < 9262 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9134
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 9134) (by omega)
  rwa [show 9134 + (i - 9134) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 6318 ≤ i → i < 9390 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9262
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 9262) (by omega)
  rwa [show 9262 + (i - 9262) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 6318 ≤ i → i < 9518 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9390
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 9390) (by omega)
  rwa [show 9390 + (i - 9390) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 6318 ≤ i → i < 9646 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9518
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 9518) (by omega)
  rwa [show 9518 + (i - 9518) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 6318 ≤ i → i < 9774 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9646
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 9646) (by omega)
  rwa [show 9646 + (i - 9646) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 6318 ≤ i → i < 9788 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9774
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 9774) (by omega)
  rwa [show 9774 + (i - 9774) = i by omega] at hk

/-- Check S3_21_193_t47: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 6318 9788 9787
    initUpTo_49 stepUpTo_27 (by decide) final_ok z hz

end UC85.W.C.S3_21_193_t47
