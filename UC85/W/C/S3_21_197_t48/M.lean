import UC85.W.C.S3_21_197_t48.Tab
import UC85.W.C.S3_21_197_t48.I0
import UC85.W.C.S3_21_197_t48.I1
import UC85.W.C.S3_21_197_t48.I2
import UC85.W.C.S3_21_197_t48.I3
import UC85.W.C.S3_21_197_t48.S0
import UC85.W.C.S3_21_197_t48.S1
import UC85.W.C.S3_21_197_t48.S2
import UC85.W.C.S3_21_197_t48.S3
import UC85.W.C.S3_21_197_t48.S4
import UC85.W.C.S3_21_197_t48.S5
import UC85.W.C.S3_21_197_t48.S6
import UC85.W.C.S3_21_197_t48.S7
import UC85.W.C.S3_21_197_t48.S8
import UC85.W.C.S3_21_197_t48.S9
import UC85.W.C.S3_21_197_t48.S10
import UC85.W.C.S3_21_197_t48.S11
import UC85.W.C.S3_21_197_t48.S12
import UC85.W.C.S3_21_197_t48.S13
import UC85.W.C.S3_21_197_t48.S14
import UC85.W.C.S3_21_197_t48.S15
import UC85.W.C.S3_21_197_t48.S16
import UC85.W.C.S3_21_197_t48.S17
import UC85.W.C.S3_21_197_t48.S18
import UC85.W.C.S3_21_197_t48.S19
import UC85.W.C.S3_21_197_t48.S20
import UC85.W.C.S3_21_197_t48.S21
import UC85.W.C.S3_21_197_t48.S22
import UC85.W.C.S3_21_197_t48.S23
import UC85.W.C.S3_21_197_t48.S24
import UC85.W.C.S3_21_197_t48.S25
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_197_t48
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

theorem initUpTo_49 : ∀ i, i < 6400 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6272
  · exact initUpTo_48 i h
  have hk := oBlock49 (i - 6272) (by omega)
  rwa [show 6272 + (i - 6272) = i by omega] at hk

theorem initUpTo_50 : ∀ i, i < 6528 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6400
  · exact initUpTo_49 i h
  have hk := oBlock50 (i - 6400) (by omega)
  rwa [show 6400 + (i - 6400) = i by omega] at hk

theorem initUpTo_51 : ∀ i, i < 6656 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6528
  · exact initUpTo_50 i h
  have hk := oBlock51 (i - 6528) (by omega)
  rwa [show 6528 + (i - 6528) = i by omega] at hk

theorem initUpTo_52 : ∀ i, i < 6784 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6656
  · exact initUpTo_51 i h
  have hk := oBlock52 (i - 6656) (by omega)
  rwa [show 6656 + (i - 6656) = i by omega] at hk

theorem initUpTo_53 : ∀ i, i < 6912 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6784
  · exact initUpTo_52 i h
  have hk := oBlock53 (i - 6784) (by omega)
  rwa [show 6784 + (i - 6784) = i by omega] at hk

theorem initUpTo_54 : ∀ i, i < 7040 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 6912
  · exact initUpTo_53 i h
  have hk := oBlock54 (i - 6912) (by omega)
  rwa [show 6912 + (i - 6912) = i by omega] at hk

theorem initUpTo_55 : ∀ i, i < 7168 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7040
  · exact initUpTo_54 i h
  have hk := oBlock55 (i - 7040) (by omega)
  rwa [show 7040 + (i - 7040) = i by omega] at hk

theorem initUpTo_56 : ∀ i, i < 7296 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7168
  · exact initUpTo_55 i h
  have hk := oBlock56 (i - 7168) (by omega)
  rwa [show 7168 + (i - 7168) = i by omega] at hk

theorem initUpTo_57 : ∀ i, i < 7424 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7296
  · exact initUpTo_56 i h
  have hk := oBlock57 (i - 7296) (by omega)
  rwa [show 7296 + (i - 7296) = i by omega] at hk

theorem initUpTo_58 : ∀ i, i < 7552 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7424
  · exact initUpTo_57 i h
  have hk := oBlock58 (i - 7424) (by omega)
  rwa [show 7424 + (i - 7424) = i by omega] at hk

theorem initUpTo_59 : ∀ i, i < 7680 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7552
  · exact initUpTo_58 i h
  have hk := oBlock59 (i - 7552) (by omega)
  rwa [show 7552 + (i - 7552) = i by omega] at hk

theorem initUpTo_60 : ∀ i, i < 7808 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7680
  · exact initUpTo_59 i h
  have hk := oBlock60 (i - 7680) (by omega)
  rwa [show 7680 + (i - 7680) = i by omega] at hk

theorem initUpTo_61 : ∀ i, i < 7936 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7808
  · exact initUpTo_60 i h
  have hk := oBlock61 (i - 7808) (by omega)
  rwa [show 7808 + (i - 7808) = i by omega] at hk

theorem initUpTo_62 : ∀ i, i < 8056 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7936
  · exact initUpTo_61 i h
  have hk := oBlock62 (i - 7936) (by omega)
  rwa [show 7936 + (i - 7936) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 8056 ≤ i → i < 8184 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 8056) (by omega)
  rwa [show 8056 + (i - 8056) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 8056 ≤ i → i < 8312 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8184
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 8184) (by omega)
  rwa [show 8184 + (i - 8184) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 8056 ≤ i → i < 8440 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8312
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 8312) (by omega)
  rwa [show 8312 + (i - 8312) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 8056 ≤ i → i < 8568 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8440
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 8440) (by omega)
  rwa [show 8440 + (i - 8440) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 8056 ≤ i → i < 8696 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8568
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 8568) (by omega)
  rwa [show 8568 + (i - 8568) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 8056 ≤ i → i < 8824 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8696
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 8696) (by omega)
  rwa [show 8696 + (i - 8696) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 8056 ≤ i → i < 8952 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8824
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 8824) (by omega)
  rwa [show 8824 + (i - 8824) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 8056 ≤ i → i < 9080 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 8952
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 8952) (by omega)
  rwa [show 8952 + (i - 8952) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 8056 ≤ i → i < 9208 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9080
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 9080) (by omega)
  rwa [show 9080 + (i - 9080) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 8056 ≤ i → i < 9336 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9208
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 9208) (by omega)
  rwa [show 9208 + (i - 9208) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 8056 ≤ i → i < 9464 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9336
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 9336) (by omega)
  rwa [show 9336 + (i - 9336) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 8056 ≤ i → i < 9592 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9464
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 9464) (by omega)
  rwa [show 9464 + (i - 9464) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 8056 ≤ i → i < 9720 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9592
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 9592) (by omega)
  rwa [show 9592 + (i - 9592) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 8056 ≤ i → i < 9848 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9720
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 9720) (by omega)
  rwa [show 9720 + (i - 9720) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 8056 ≤ i → i < 9976 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9848
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 9848) (by omega)
  rwa [show 9848 + (i - 9848) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 8056 ≤ i → i < 10104 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9976
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 9976) (by omega)
  rwa [show 9976 + (i - 9976) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 8056 ≤ i → i < 10232 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10104
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 10104) (by omega)
  rwa [show 10104 + (i - 10104) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 8056 ≤ i → i < 10360 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10232
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 10232) (by omega)
  rwa [show 10232 + (i - 10232) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 8056 ≤ i → i < 10488 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10360
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 10360) (by omega)
  rwa [show 10360 + (i - 10360) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 8056 ≤ i → i < 10616 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10488
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 10488) (by omega)
  rwa [show 10488 + (i - 10488) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 8056 ≤ i → i < 10744 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10616
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 10616) (by omega)
  rwa [show 10616 + (i - 10616) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 8056 ≤ i → i < 10872 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10744
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 10744) (by omega)
  rwa [show 10744 + (i - 10744) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 8056 ≤ i → i < 11000 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10872
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 10872) (by omega)
  rwa [show 10872 + (i - 10872) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 8056 ≤ i → i < 11128 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11000
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 11000) (by omega)
  rwa [show 11000 + (i - 11000) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 8056 ≤ i → i < 11256 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11128
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 11128) (by omega)
  rwa [show 11128 + (i - 11128) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 8056 ≤ i → i < 11358 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11256
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 11256) (by omega)
  rwa [show 11256 + (i - 11256) = i by omega] at hk

/-- Check S3_21_197_t48: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 8056 11358 11357
    initUpTo_62 stepUpTo_25 (by decide) final_ok z hz

end UC85.W.C.S3_21_197_t48
