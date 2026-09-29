import UC85.W.C.S3_16_t19.Tab
import UC85.W.C.S3_16_t19.I0
import UC85.W.C.S3_16_t19.I1
import UC85.W.C.S3_16_t19.I2
import UC85.W.C.S3_16_t19.I3
import UC85.W.C.S3_16_t19.I4
import UC85.W.C.S3_16_t19.S0
import UC85.W.C.S3_16_t19.S1
import UC85.W.C.S3_16_t19.S2
import UC85.W.C.S3_16_t19.S3
import UC85.W.C.S3_16_t19.S4
import UC85.W.C.S3_16_t19.S5
import UC85.W.C.S3_16_t19.S6
import UC85.W.C.S3_16_t19.S7
import UC85.W.C.S3_16_t19.S8
import UC85.W.C.S3_16_t19.S9
import UC85.W.C.S3_16_t19.S10
import UC85.W.C.S3_16_t19.S11
import UC85.W.C.S3_16_t19.S12
import UC85.W.C.S3_16_t19.S13
import UC85.W.C.S3_16_t19.S14
import UC85.W.C.S3_16_t19.S15
import UC85.W.C.S3_16_t19.S16
import UC85.W.C.S3_16_t19.S17
import UC85.W.C.S3_16_t19.S18
import UC85.W.C.S3_16_t19.S19
import UC85.W.C.S3_16_t19.S20
import UC85.W.C.S3_16_t19.S21
import UC85.W.C.S3_16_t19.S22
import UC85.W.C.S3_16_t19.S23
import UC85.W.C.S3_16_t19.S24
import UC85.W.C.S3_16_t19.S25
import UC85.W.C.S3_16_t19.S26
import UC85.W.C.S3_16_t19.S27
import UC85.W.C.S3_16_t19.S28
import UC85.W.C.S3_16_t19.S29
import UC85.W.C.S3_16_t19.S30
import UC85.W.C.S3_16_t19.S31
import UC85.W.C.S3_16_t19.S32
import UC85.W.C.S3_16_t19.S33
import UC85.W.C.S3_16_t19.S34
import UC85.W.C.S3_16_t19.S35
import UC85.W.C.S3_16_t19.S36
import UC85.W.C.S3_16_t19.S37
import UC85.W.C.S3_16_t19.S38
import UC85.W.C.S3_16_t19.S39
import UC85.W.C.S3_16_t19.S40
import UC85.W.C.S3_16_t19.S41
import UC85.W.C.S3_16_t19.S42
import UC85.W.C.S3_16_t19.S43
import UC85.W.C.S3_16_t19.S44
import UC85.W.C.S3_16_t19.S45
import UC85.W.C.S3_16_t19.S46
import UC85.W.C.S3_16_t19.S47
import UC85.W.C.S3_16_t19.S48
import UC85.W.C.S3_16_t19.S49
import UC85.W.C.S3_16_t19.S50
import UC85.W.C.S3_16_t19.S51
import UC85.W.C.S3_16_t19.S52
import UC85.W.C.S3_16_t19.S53
import UC85.W.C.S3_16_t19.S54
import UC85.W.C.S3_16_t19.S55
import UC85.W.C.S3_16_t19.S56
import UC85.W.C.S3_16_t19.S57
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_16_t19
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

theorem initUpTo_73 : ∀ i, i < 9460 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9344
  · exact initUpTo_72 i h
  have hk := oBlock73 (i - 9344) (by omega)
  rwa [show 9344 + (i - 9344) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 9460 ≤ i → i < 9588 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 9460) (by omega)
  rwa [show 9460 + (i - 9460) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 9460 ≤ i → i < 9716 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9588
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 9588) (by omega)
  rwa [show 9588 + (i - 9588) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 9460 ≤ i → i < 9844 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9716
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 9716) (by omega)
  rwa [show 9716 + (i - 9716) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 9460 ≤ i → i < 9972 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9844
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 9844) (by omega)
  rwa [show 9844 + (i - 9844) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 9460 ≤ i → i < 10100 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 9972
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 9972) (by omega)
  rwa [show 9972 + (i - 9972) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 9460 ≤ i → i < 10228 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10100
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 10100) (by omega)
  rwa [show 10100 + (i - 10100) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 9460 ≤ i → i < 10356 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10228
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 10228) (by omega)
  rwa [show 10228 + (i - 10228) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 9460 ≤ i → i < 10484 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10356
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 10356) (by omega)
  rwa [show 10356 + (i - 10356) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 9460 ≤ i → i < 10612 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10484
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 10484) (by omega)
  rwa [show 10484 + (i - 10484) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 9460 ≤ i → i < 10740 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10612
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 10612) (by omega)
  rwa [show 10612 + (i - 10612) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 9460 ≤ i → i < 10868 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10740
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 10740) (by omega)
  rwa [show 10740 + (i - 10740) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 9460 ≤ i → i < 10996 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10868
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 10868) (by omega)
  rwa [show 10868 + (i - 10868) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 9460 ≤ i → i < 11124 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10996
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 10996) (by omega)
  rwa [show 10996 + (i - 10996) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 9460 ≤ i → i < 11252 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11124
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 11124) (by omega)
  rwa [show 11124 + (i - 11124) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 9460 ≤ i → i < 11380 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11252
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 11252) (by omega)
  rwa [show 11252 + (i - 11252) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 9460 ≤ i → i < 11508 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11380
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 11380) (by omega)
  rwa [show 11380 + (i - 11380) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 9460 ≤ i → i < 11636 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11508
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 11508) (by omega)
  rwa [show 11508 + (i - 11508) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 9460 ≤ i → i < 11764 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11636
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 11636) (by omega)
  rwa [show 11636 + (i - 11636) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 9460 ≤ i → i < 11892 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11764
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 11764) (by omega)
  rwa [show 11764 + (i - 11764) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 9460 ≤ i → i < 12020 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11892
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 11892) (by omega)
  rwa [show 11892 + (i - 11892) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 9460 ≤ i → i < 12148 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12020
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 12020) (by omega)
  rwa [show 12020 + (i - 12020) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 9460 ≤ i → i < 12276 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12148
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 12148) (by omega)
  rwa [show 12148 + (i - 12148) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 9460 ≤ i → i < 12404 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12276
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 12276) (by omega)
  rwa [show 12276 + (i - 12276) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 9460 ≤ i → i < 12532 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12404
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 12404) (by omega)
  rwa [show 12404 + (i - 12404) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 9460 ≤ i → i < 12660 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12532
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 12532) (by omega)
  rwa [show 12532 + (i - 12532) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 9460 ≤ i → i < 12788 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12660
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 12660) (by omega)
  rwa [show 12660 + (i - 12660) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 9460 ≤ i → i < 12916 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12788
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 12788) (by omega)
  rwa [show 12788 + (i - 12788) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 9460 ≤ i → i < 13044 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12916
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 12916) (by omega)
  rwa [show 12916 + (i - 12916) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 9460 ≤ i → i < 13172 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13044
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 13044) (by omega)
  rwa [show 13044 + (i - 13044) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 9460 ≤ i → i < 13300 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13172
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 13172) (by omega)
  rwa [show 13172 + (i - 13172) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 9460 ≤ i → i < 13428 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13300
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 13300) (by omega)
  rwa [show 13300 + (i - 13300) = i by omega] at hk

theorem stepUpTo_31 : ∀ i, 9460 ≤ i → i < 13556 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13428
  · exact stepUpTo_30 i hlo h
  have hk := sBlock31 (i - 13428) (by omega)
  rwa [show 13428 + (i - 13428) = i by omega] at hk

theorem stepUpTo_32 : ∀ i, 9460 ≤ i → i < 13684 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13556
  · exact stepUpTo_31 i hlo h
  have hk := sBlock32 (i - 13556) (by omega)
  rwa [show 13556 + (i - 13556) = i by omega] at hk

theorem stepUpTo_33 : ∀ i, 9460 ≤ i → i < 13812 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13684
  · exact stepUpTo_32 i hlo h
  have hk := sBlock33 (i - 13684) (by omega)
  rwa [show 13684 + (i - 13684) = i by omega] at hk

theorem stepUpTo_34 : ∀ i, 9460 ≤ i → i < 13940 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13812
  · exact stepUpTo_33 i hlo h
  have hk := sBlock34 (i - 13812) (by omega)
  rwa [show 13812 + (i - 13812) = i by omega] at hk

theorem stepUpTo_35 : ∀ i, 9460 ≤ i → i < 14068 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13940
  · exact stepUpTo_34 i hlo h
  have hk := sBlock35 (i - 13940) (by omega)
  rwa [show 13940 + (i - 13940) = i by omega] at hk

theorem stepUpTo_36 : ∀ i, 9460 ≤ i → i < 14196 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14068
  · exact stepUpTo_35 i hlo h
  have hk := sBlock36 (i - 14068) (by omega)
  rwa [show 14068 + (i - 14068) = i by omega] at hk

theorem stepUpTo_37 : ∀ i, 9460 ≤ i → i < 14324 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14196
  · exact stepUpTo_36 i hlo h
  have hk := sBlock37 (i - 14196) (by omega)
  rwa [show 14196 + (i - 14196) = i by omega] at hk

theorem stepUpTo_38 : ∀ i, 9460 ≤ i → i < 14452 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14324
  · exact stepUpTo_37 i hlo h
  have hk := sBlock38 (i - 14324) (by omega)
  rwa [show 14324 + (i - 14324) = i by omega] at hk

theorem stepUpTo_39 : ∀ i, 9460 ≤ i → i < 14580 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14452
  · exact stepUpTo_38 i hlo h
  have hk := sBlock39 (i - 14452) (by omega)
  rwa [show 14452 + (i - 14452) = i by omega] at hk

theorem stepUpTo_40 : ∀ i, 9460 ≤ i → i < 14708 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14580
  · exact stepUpTo_39 i hlo h
  have hk := sBlock40 (i - 14580) (by omega)
  rwa [show 14580 + (i - 14580) = i by omega] at hk

theorem stepUpTo_41 : ∀ i, 9460 ≤ i → i < 14836 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14708
  · exact stepUpTo_40 i hlo h
  have hk := sBlock41 (i - 14708) (by omega)
  rwa [show 14708 + (i - 14708) = i by omega] at hk

theorem stepUpTo_42 : ∀ i, 9460 ≤ i → i < 14964 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14836
  · exact stepUpTo_41 i hlo h
  have hk := sBlock42 (i - 14836) (by omega)
  rwa [show 14836 + (i - 14836) = i by omega] at hk

theorem stepUpTo_43 : ∀ i, 9460 ≤ i → i < 15092 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14964
  · exact stepUpTo_42 i hlo h
  have hk := sBlock43 (i - 14964) (by omega)
  rwa [show 14964 + (i - 14964) = i by omega] at hk

theorem stepUpTo_44 : ∀ i, 9460 ≤ i → i < 15220 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15092
  · exact stepUpTo_43 i hlo h
  have hk := sBlock44 (i - 15092) (by omega)
  rwa [show 15092 + (i - 15092) = i by omega] at hk

theorem stepUpTo_45 : ∀ i, 9460 ≤ i → i < 15348 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15220
  · exact stepUpTo_44 i hlo h
  have hk := sBlock45 (i - 15220) (by omega)
  rwa [show 15220 + (i - 15220) = i by omega] at hk

theorem stepUpTo_46 : ∀ i, 9460 ≤ i → i < 15476 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15348
  · exact stepUpTo_45 i hlo h
  have hk := sBlock46 (i - 15348) (by omega)
  rwa [show 15348 + (i - 15348) = i by omega] at hk

theorem stepUpTo_47 : ∀ i, 9460 ≤ i → i < 15604 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15476
  · exact stepUpTo_46 i hlo h
  have hk := sBlock47 (i - 15476) (by omega)
  rwa [show 15476 + (i - 15476) = i by omega] at hk

theorem stepUpTo_48 : ∀ i, 9460 ≤ i → i < 15732 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15604
  · exact stepUpTo_47 i hlo h
  have hk := sBlock48 (i - 15604) (by omega)
  rwa [show 15604 + (i - 15604) = i by omega] at hk

theorem stepUpTo_49 : ∀ i, 9460 ≤ i → i < 15860 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15732
  · exact stepUpTo_48 i hlo h
  have hk := sBlock49 (i - 15732) (by omega)
  rwa [show 15732 + (i - 15732) = i by omega] at hk

theorem stepUpTo_50 : ∀ i, 9460 ≤ i → i < 15988 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15860
  · exact stepUpTo_49 i hlo h
  have hk := sBlock50 (i - 15860) (by omega)
  rwa [show 15860 + (i - 15860) = i by omega] at hk

theorem stepUpTo_51 : ∀ i, 9460 ≤ i → i < 16116 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15988
  · exact stepUpTo_50 i hlo h
  have hk := sBlock51 (i - 15988) (by omega)
  rwa [show 15988 + (i - 15988) = i by omega] at hk

theorem stepUpTo_52 : ∀ i, 9460 ≤ i → i < 16244 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16116
  · exact stepUpTo_51 i hlo h
  have hk := sBlock52 (i - 16116) (by omega)
  rwa [show 16116 + (i - 16116) = i by omega] at hk

theorem stepUpTo_53 : ∀ i, 9460 ≤ i → i < 16372 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16244
  · exact stepUpTo_52 i hlo h
  have hk := sBlock53 (i - 16244) (by omega)
  rwa [show 16244 + (i - 16244) = i by omega] at hk

theorem stepUpTo_54 : ∀ i, 9460 ≤ i → i < 16500 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16372
  · exact stepUpTo_53 i hlo h
  have hk := sBlock54 (i - 16372) (by omega)
  rwa [show 16372 + (i - 16372) = i by omega] at hk

theorem stepUpTo_55 : ∀ i, 9460 ≤ i → i < 16628 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16500
  · exact stepUpTo_54 i hlo h
  have hk := sBlock55 (i - 16500) (by omega)
  rwa [show 16500 + (i - 16500) = i by omega] at hk

theorem stepUpTo_56 : ∀ i, 9460 ≤ i → i < 16756 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16628
  · exact stepUpTo_55 i hlo h
  have hk := sBlock56 (i - 16628) (by omega)
  rwa [show 16628 + (i - 16628) = i by omega] at hk

theorem stepUpTo_57 : ∀ i, 9460 ≤ i → i < 16760 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16756
  · exact stepUpTo_56 i hlo h
  have hk := sBlock57 (i - 16756) (by omega)
  rwa [show 16756 + (i - 16756) = i by omega] at hk

/-- Check S3_16_t19: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 9460 16760 16759
    initUpTo_73 stepUpTo_57 (by decide) final_ok z hz

end UC85.W.C.S3_16_t19
