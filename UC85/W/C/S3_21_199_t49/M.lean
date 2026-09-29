import UC85.W.C.S3_21_199_t49.Tab
import UC85.W.C.S3_21_199_t49.I0
import UC85.W.C.S3_21_199_t49.I1
import UC85.W.C.S3_21_199_t49.I2
import UC85.W.C.S3_21_199_t49.I3
import UC85.W.C.S3_21_199_t49.I4
import UC85.W.C.S3_21_199_t49.S0
import UC85.W.C.S3_21_199_t49.S1
import UC85.W.C.S3_21_199_t49.S2
import UC85.W.C.S3_21_199_t49.S3
import UC85.W.C.S3_21_199_t49.S4
import UC85.W.C.S3_21_199_t49.S5
import UC85.W.C.S3_21_199_t49.S6
import UC85.W.C.S3_21_199_t49.S7
import UC85.W.C.S3_21_199_t49.S8
import UC85.W.C.S3_21_199_t49.S9
import UC85.W.C.S3_21_199_t49.S10
import UC85.W.C.S3_21_199_t49.S11
import UC85.W.C.S3_21_199_t49.S12
import UC85.W.C.S3_21_199_t49.S13
import UC85.W.C.S3_21_199_t49.S14
import UC85.W.C.S3_21_199_t49.S15
import UC85.W.C.S3_21_199_t49.S16
import UC85.W.C.S3_21_199_t49.S17
import UC85.W.C.S3_21_199_t49.S18
import UC85.W.C.S3_21_199_t49.S19
import UC85.W.C.S3_21_199_t49.S20
import UC85.W.C.S3_21_199_t49.S21
import UC85.W.C.S3_21_199_t49.S22
import UC85.W.C.S3_21_199_t49.S23
import UC85.W.C.S3_21_199_t49.S24
import UC85.W.C.S3_21_199_t49.S25
import UC85.W.C.S3_21_199_t49.S26
import UC85.W.C.S3_21_199_t49.S27
import UC85.W.C.S3_21_199_t49.S28
import UC85.W.C.S3_21_199_t49.S29
import UC85.W.C.S3_21_199_t49.S30
import UC85.W.C.S3_21_199_t49.S31
import UC85.W.C.S3_21_199_t49.S32
import UC85.W.C.S3_21_199_t49.S33
import UC85.W.C.S3_21_199_t49.S34
import UC85.W.C.S3_21_199_t49.S35
import UC85.W.C.S3_21_199_t49.S36
import UC85.W.C.S3_21_199_t49.S37
import UC85.W.C.S3_21_199_t49.S38
import UC85.W.C.S3_21_199_t49.S39
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_199_t49
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

theorem initUpTo_62 : ∀ i, i < 8064 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 7936
  · exact initUpTo_61 i h
  have hk := oBlock62 (i - 7936) (by omega)
  rwa [show 7936 + (i - 7936) = i by omega] at hk

theorem initUpTo_63 : ∀ i, i < 8192 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8064
  · exact initUpTo_62 i h
  have hk := oBlock63 (i - 8064) (by omega)
  rwa [show 8064 + (i - 8064) = i by omega] at hk

theorem initUpTo_64 : ∀ i, i < 8320 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8192
  · exact initUpTo_63 i h
  have hk := oBlock64 (i - 8192) (by omega)
  rwa [show 8192 + (i - 8192) = i by omega] at hk

theorem initUpTo_65 : ∀ i, i < 8448 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8320
  · exact initUpTo_64 i h
  have hk := oBlock65 (i - 8320) (by omega)
  rwa [show 8320 + (i - 8320) = i by omega] at hk

theorem initUpTo_66 : ∀ i, i < 8576 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8448
  · exact initUpTo_65 i h
  have hk := oBlock66 (i - 8448) (by omega)
  rwa [show 8448 + (i - 8448) = i by omega] at hk

theorem initUpTo_67 : ∀ i, i < 8704 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8576
  · exact initUpTo_66 i h
  have hk := oBlock67 (i - 8576) (by omega)
  rwa [show 8576 + (i - 8576) = i by omega] at hk

theorem initUpTo_68 : ∀ i, i < 8832 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8704
  · exact initUpTo_67 i h
  have hk := oBlock68 (i - 8704) (by omega)
  rwa [show 8704 + (i - 8704) = i by omega] at hk

theorem initUpTo_69 : ∀ i, i < 8960 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8832
  · exact initUpTo_68 i h
  have hk := oBlock69 (i - 8832) (by omega)
  rwa [show 8832 + (i - 8832) = i by omega] at hk

theorem initUpTo_70 : ∀ i, i < 9088 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 8960
  · exact initUpTo_69 i h
  have hk := oBlock70 (i - 8960) (by omega)
  rwa [show 8960 + (i - 8960) = i by omega] at hk

theorem initUpTo_71 : ∀ i, i < 9216 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9088
  · exact initUpTo_70 i h
  have hk := oBlock71 (i - 9088) (by omega)
  rwa [show 9088 + (i - 9088) = i by omega] at hk

theorem initUpTo_72 : ∀ i, i < 9344 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9216
  · exact initUpTo_71 i h
  have hk := oBlock72 (i - 9216) (by omega)
  rwa [show 9216 + (i - 9216) = i by omega] at hk

theorem initUpTo_73 : ∀ i, i < 9472 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9344
  · exact initUpTo_72 i h
  have hk := oBlock73 (i - 9344) (by omega)
  rwa [show 9344 + (i - 9344) = i by omega] at hk

theorem initUpTo_74 : ∀ i, i < 9600 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9472
  · exact initUpTo_73 i h
  have hk := oBlock74 (i - 9472) (by omega)
  rwa [show 9472 + (i - 9472) = i by omega] at hk

theorem initUpTo_75 : ∀ i, i < 9728 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9600
  · exact initUpTo_74 i h
  have hk := oBlock75 (i - 9600) (by omega)
  rwa [show 9600 + (i - 9600) = i by omega] at hk

theorem initUpTo_76 : ∀ i, i < 9856 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9728
  · exact initUpTo_75 i h
  have hk := oBlock76 (i - 9728) (by omega)
  rwa [show 9728 + (i - 9728) = i by omega] at hk

theorem initUpTo_77 : ∀ i, i < 9976 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9856
  · exact initUpTo_76 i h
  have hk := oBlock77 (i - 9856) (by omega)
  rwa [show 9856 + (i - 9856) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 9976 ≤ i → i < 10104 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 9976) (by omega)
  rwa [show 9976 + (i - 9976) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 9976 ≤ i → i < 10232 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10104
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 10104) (by omega)
  rwa [show 10104 + (i - 10104) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 9976 ≤ i → i < 10360 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10232
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 10232) (by omega)
  rwa [show 10232 + (i - 10232) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 9976 ≤ i → i < 10488 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10360
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 10360) (by omega)
  rwa [show 10360 + (i - 10360) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 9976 ≤ i → i < 10616 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10488
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 10488) (by omega)
  rwa [show 10488 + (i - 10488) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 9976 ≤ i → i < 10744 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10616
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 10616) (by omega)
  rwa [show 10616 + (i - 10616) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 9976 ≤ i → i < 10872 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10744
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 10744) (by omega)
  rwa [show 10744 + (i - 10744) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 9976 ≤ i → i < 11000 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10872
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 10872) (by omega)
  rwa [show 10872 + (i - 10872) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 9976 ≤ i → i < 11128 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11000
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 11000) (by omega)
  rwa [show 11000 + (i - 11000) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 9976 ≤ i → i < 11256 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11128
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 11128) (by omega)
  rwa [show 11128 + (i - 11128) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 9976 ≤ i → i < 11384 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11256
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 11256) (by omega)
  rwa [show 11256 + (i - 11256) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 9976 ≤ i → i < 11512 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11384
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 11384) (by omega)
  rwa [show 11384 + (i - 11384) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 9976 ≤ i → i < 11640 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11512
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 11512) (by omega)
  rwa [show 11512 + (i - 11512) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 9976 ≤ i → i < 11768 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11640
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 11640) (by omega)
  rwa [show 11640 + (i - 11640) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 9976 ≤ i → i < 11896 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11768
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 11768) (by omega)
  rwa [show 11768 + (i - 11768) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 9976 ≤ i → i < 12024 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11896
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 11896) (by omega)
  rwa [show 11896 + (i - 11896) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 9976 ≤ i → i < 12152 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12024
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 12024) (by omega)
  rwa [show 12024 + (i - 12024) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 9976 ≤ i → i < 12280 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12152
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 12152) (by omega)
  rwa [show 12152 + (i - 12152) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 9976 ≤ i → i < 12408 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12280
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 12280) (by omega)
  rwa [show 12280 + (i - 12280) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 9976 ≤ i → i < 12536 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12408
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 12408) (by omega)
  rwa [show 12408 + (i - 12408) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 9976 ≤ i → i < 12664 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12536
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 12536) (by omega)
  rwa [show 12536 + (i - 12536) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 9976 ≤ i → i < 12792 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12664
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 12664) (by omega)
  rwa [show 12664 + (i - 12664) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 9976 ≤ i → i < 12920 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12792
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 12792) (by omega)
  rwa [show 12792 + (i - 12792) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 9976 ≤ i → i < 13048 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12920
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 12920) (by omega)
  rwa [show 12920 + (i - 12920) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 9976 ≤ i → i < 13176 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13048
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 13048) (by omega)
  rwa [show 13048 + (i - 13048) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 9976 ≤ i → i < 13304 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13176
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 13176) (by omega)
  rwa [show 13176 + (i - 13176) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 9976 ≤ i → i < 13432 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13304
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 13304) (by omega)
  rwa [show 13304 + (i - 13304) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 9976 ≤ i → i < 13560 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13432
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 13432) (by omega)
  rwa [show 13432 + (i - 13432) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 9976 ≤ i → i < 13688 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13560
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 13560) (by omega)
  rwa [show 13560 + (i - 13560) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 9976 ≤ i → i < 13816 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13688
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 13688) (by omega)
  rwa [show 13688 + (i - 13688) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 9976 ≤ i → i < 13944 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13816
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 13816) (by omega)
  rwa [show 13816 + (i - 13816) = i by omega] at hk

theorem stepUpTo_31 : ∀ i, 9976 ≤ i → i < 14072 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13944
  · exact stepUpTo_30 i hlo h
  have hk := sBlock31 (i - 13944) (by omega)
  rwa [show 13944 + (i - 13944) = i by omega] at hk

theorem stepUpTo_32 : ∀ i, 9976 ≤ i → i < 14200 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14072
  · exact stepUpTo_31 i hlo h
  have hk := sBlock32 (i - 14072) (by omega)
  rwa [show 14072 + (i - 14072) = i by omega] at hk

theorem stepUpTo_33 : ∀ i, 9976 ≤ i → i < 14328 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14200
  · exact stepUpTo_32 i hlo h
  have hk := sBlock33 (i - 14200) (by omega)
  rwa [show 14200 + (i - 14200) = i by omega] at hk

theorem stepUpTo_34 : ∀ i, 9976 ≤ i → i < 14456 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14328
  · exact stepUpTo_33 i hlo h
  have hk := sBlock34 (i - 14328) (by omega)
  rwa [show 14328 + (i - 14328) = i by omega] at hk

theorem stepUpTo_35 : ∀ i, 9976 ≤ i → i < 14584 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14456
  · exact stepUpTo_34 i hlo h
  have hk := sBlock35 (i - 14456) (by omega)
  rwa [show 14456 + (i - 14456) = i by omega] at hk

theorem stepUpTo_36 : ∀ i, 9976 ≤ i → i < 14712 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14584
  · exact stepUpTo_35 i hlo h
  have hk := sBlock36 (i - 14584) (by omega)
  rwa [show 14584 + (i - 14584) = i by omega] at hk

theorem stepUpTo_37 : ∀ i, 9976 ≤ i → i < 14840 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14712
  · exact stepUpTo_36 i hlo h
  have hk := sBlock37 (i - 14712) (by omega)
  rwa [show 14712 + (i - 14712) = i by omega] at hk

theorem stepUpTo_38 : ∀ i, 9976 ≤ i → i < 14968 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14840
  · exact stepUpTo_37 i hlo h
  have hk := sBlock38 (i - 14840) (by omega)
  rwa [show 14840 + (i - 14840) = i by omega] at hk

theorem stepUpTo_39 : ∀ i, 9976 ≤ i → i < 15066 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14968
  · exact stepUpTo_38 i hlo h
  have hk := sBlock39 (i - 14968) (by omega)
  rwa [show 14968 + (i - 14968) = i by omega] at hk

/-- Check S3_21_199_t49: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 9976 15066 15065
    initUpTo_77 stepUpTo_39 (by decide) final_ok z hz

end UC85.W.C.S3_21_199_t49
