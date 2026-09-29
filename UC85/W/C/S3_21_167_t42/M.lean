import UC85.W.C.S3_21_167_t42.Tab
import UC85.W.C.S3_21_167_t42.I0
import UC85.W.C.S3_21_167_t42.I1
import UC85.W.C.S3_21_167_t42.I2
import UC85.W.C.S3_21_167_t42.I3
import UC85.W.C.S3_21_167_t42.I4
import UC85.W.C.S3_21_167_t42.S0
import UC85.W.C.S3_21_167_t42.S1
import UC85.W.C.S3_21_167_t42.S2
import UC85.W.C.S3_21_167_t42.S3
import UC85.W.C.S3_21_167_t42.S4
import UC85.W.C.S3_21_167_t42.S5
import UC85.W.C.S3_21_167_t42.S6
import UC85.W.C.S3_21_167_t42.S7
import UC85.W.C.S3_21_167_t42.S8
import UC85.W.C.S3_21_167_t42.S9
import UC85.W.C.S3_21_167_t42.S10
import UC85.W.C.S3_21_167_t42.S11
import UC85.W.C.S3_21_167_t42.S12
import UC85.W.C.S3_21_167_t42.S13
import UC85.W.C.S3_21_167_t42.S14
import UC85.W.C.S3_21_167_t42.S15
import UC85.W.C.S3_21_167_t42.S16
import UC85.W.C.S3_21_167_t42.S17
import UC85.W.C.S3_21_167_t42.S18
import UC85.W.C.S3_21_167_t42.S19
import UC85.W.C.S3_21_167_t42.S20
import UC85.W.C.S3_21_167_t42.S21
import UC85.W.C.S3_21_167_t42.S22
import UC85.W.C.S3_21_167_t42.S23
import UC85.W.C.S3_21_167_t42.S24
import UC85.W.C.S3_21_167_t42.S25
import UC85.W.C.S3_21_167_t42.S26
import UC85.W.C.S3_21_167_t42.S27
import UC85.W.C.S3_21_167_t42.S28
import UC85.W.C.S3_21_167_t42.S29
import UC85.W.C.S3_21_167_t42.S30
import UC85.W.C.S3_21_167_t42.S31
import UC85.W.C.S3_21_167_t42.S32
import UC85.W.C.S3_21_167_t42.S33
import UC85.W.C.S3_21_167_t42.S34
import UC85.W.C.S3_21_167_t42.S35
import UC85.W.C.S3_21_167_t42.S36
import UC85.W.C.S3_21_167_t42.S37
import UC85.W.C.S3_21_167_t42.S38
import UC85.W.C.S3_21_167_t42.S39
import UC85.W.C.S3_21_167_t42.S40
import UC85.W.C.S3_21_167_t42.S41
import UC85.W.C.S3_21_167_t42.S42
import UC85.W.C.S3_21_167_t42.S43
import UC85.W.C.S3_21_167_t42.S44
import UC85.W.C.S3_21_167_t42.S45
import UC85.W.C.S3_21_167_t42.S46
import UC85.W.C.S3_21_167_t42.S47
import UC85.W.C.S3_21_167_t42.S48
import UC85.W.C.S3_21_167_t42.S49
import UC85.W.C.S3_21_167_t42.S50
import UC85.W.C.S3_21_167_t42.S51
import UC85.W.C.S3_21_167_t42.S52
import UC85.W.C.S3_21_167_t42.S53
import UC85.W.C.S3_21_167_t42.S54
import UC85.W.C.S3_21_167_t42.S55
import UC85.W.C.S3_21_167_t42.S56
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_167_t42
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

theorem initUpTo_77 : ∀ i, i < 9984 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9856
  · exact initUpTo_76 i h
  have hk := oBlock77 (i - 9856) (by omega)
  rwa [show 9856 + (i - 9856) = i by omega] at hk

theorem initUpTo_78 : ∀ i, i < 10112 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 9984
  · exact initUpTo_77 i h
  have hk := oBlock78 (i - 9984) (by omega)
  rwa [show 9984 + (i - 9984) = i by omega] at hk

theorem initUpTo_79 : ∀ i, i < 10138 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10112
  · exact initUpTo_78 i h
  have hk := oBlock79 (i - 10112) (by omega)
  rwa [show 10112 + (i - 10112) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 10138 ≤ i → i < 10266 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 10138) (by omega)
  rwa [show 10138 + (i - 10138) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 10138 ≤ i → i < 10394 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10266
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 10266) (by omega)
  rwa [show 10266 + (i - 10266) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 10138 ≤ i → i < 10522 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10394
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 10394) (by omega)
  rwa [show 10394 + (i - 10394) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 10138 ≤ i → i < 10650 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10522
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 10522) (by omega)
  rwa [show 10522 + (i - 10522) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 10138 ≤ i → i < 10778 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10650
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 10650) (by omega)
  rwa [show 10650 + (i - 10650) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 10138 ≤ i → i < 10906 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10778
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 10778) (by omega)
  rwa [show 10778 + (i - 10778) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 10138 ≤ i → i < 11034 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 10906
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 10906) (by omega)
  rwa [show 10906 + (i - 10906) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 10138 ≤ i → i < 11162 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11034
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 11034) (by omega)
  rwa [show 11034 + (i - 11034) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 10138 ≤ i → i < 11290 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11162
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 11162) (by omega)
  rwa [show 11162 + (i - 11162) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 10138 ≤ i → i < 11418 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11290
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 11290) (by omega)
  rwa [show 11290 + (i - 11290) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 10138 ≤ i → i < 11546 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11418
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 11418) (by omega)
  rwa [show 11418 + (i - 11418) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 10138 ≤ i → i < 11674 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11546
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 11546) (by omega)
  rwa [show 11546 + (i - 11546) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 10138 ≤ i → i < 11802 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11674
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 11674) (by omega)
  rwa [show 11674 + (i - 11674) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 10138 ≤ i → i < 11930 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11802
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 11802) (by omega)
  rwa [show 11802 + (i - 11802) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 10138 ≤ i → i < 12058 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 11930
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 11930) (by omega)
  rwa [show 11930 + (i - 11930) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 10138 ≤ i → i < 12186 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12058
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 12058) (by omega)
  rwa [show 12058 + (i - 12058) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 10138 ≤ i → i < 12314 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12186
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 12186) (by omega)
  rwa [show 12186 + (i - 12186) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 10138 ≤ i → i < 12442 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12314
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 12314) (by omega)
  rwa [show 12314 + (i - 12314) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 10138 ≤ i → i < 12570 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12442
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 12442) (by omega)
  rwa [show 12442 + (i - 12442) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 10138 ≤ i → i < 12698 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12570
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 12570) (by omega)
  rwa [show 12570 + (i - 12570) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 10138 ≤ i → i < 12826 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12698
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 12698) (by omega)
  rwa [show 12698 + (i - 12698) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 10138 ≤ i → i < 12954 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12826
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 12826) (by omega)
  rwa [show 12826 + (i - 12826) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 10138 ≤ i → i < 13082 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12954
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 12954) (by omega)
  rwa [show 12954 + (i - 12954) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 10138 ≤ i → i < 13210 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13082
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 13082) (by omega)
  rwa [show 13082 + (i - 13082) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 10138 ≤ i → i < 13338 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13210
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 13210) (by omega)
  rwa [show 13210 + (i - 13210) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 10138 ≤ i → i < 13466 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13338
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 13338) (by omega)
  rwa [show 13338 + (i - 13338) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 10138 ≤ i → i < 13594 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13466
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 13466) (by omega)
  rwa [show 13466 + (i - 13466) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 10138 ≤ i → i < 13722 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13594
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 13594) (by omega)
  rwa [show 13594 + (i - 13594) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 10138 ≤ i → i < 13850 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13722
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 13722) (by omega)
  rwa [show 13722 + (i - 13722) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 10138 ≤ i → i < 13978 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13850
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 13850) (by omega)
  rwa [show 13850 + (i - 13850) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 10138 ≤ i → i < 14106 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13978
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 13978) (by omega)
  rwa [show 13978 + (i - 13978) = i by omega] at hk

theorem stepUpTo_31 : ∀ i, 10138 ≤ i → i < 14234 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14106
  · exact stepUpTo_30 i hlo h
  have hk := sBlock31 (i - 14106) (by omega)
  rwa [show 14106 + (i - 14106) = i by omega] at hk

theorem stepUpTo_32 : ∀ i, 10138 ≤ i → i < 14362 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14234
  · exact stepUpTo_31 i hlo h
  have hk := sBlock32 (i - 14234) (by omega)
  rwa [show 14234 + (i - 14234) = i by omega] at hk

theorem stepUpTo_33 : ∀ i, 10138 ≤ i → i < 14490 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14362
  · exact stepUpTo_32 i hlo h
  have hk := sBlock33 (i - 14362) (by omega)
  rwa [show 14362 + (i - 14362) = i by omega] at hk

theorem stepUpTo_34 : ∀ i, 10138 ≤ i → i < 14618 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14490
  · exact stepUpTo_33 i hlo h
  have hk := sBlock34 (i - 14490) (by omega)
  rwa [show 14490 + (i - 14490) = i by omega] at hk

theorem stepUpTo_35 : ∀ i, 10138 ≤ i → i < 14746 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14618
  · exact stepUpTo_34 i hlo h
  have hk := sBlock35 (i - 14618) (by omega)
  rwa [show 14618 + (i - 14618) = i by omega] at hk

theorem stepUpTo_36 : ∀ i, 10138 ≤ i → i < 14874 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14746
  · exact stepUpTo_35 i hlo h
  have hk := sBlock36 (i - 14746) (by omega)
  rwa [show 14746 + (i - 14746) = i by omega] at hk

theorem stepUpTo_37 : ∀ i, 10138 ≤ i → i < 15002 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14874
  · exact stepUpTo_36 i hlo h
  have hk := sBlock37 (i - 14874) (by omega)
  rwa [show 14874 + (i - 14874) = i by omega] at hk

theorem stepUpTo_38 : ∀ i, 10138 ≤ i → i < 15130 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15002
  · exact stepUpTo_37 i hlo h
  have hk := sBlock38 (i - 15002) (by omega)
  rwa [show 15002 + (i - 15002) = i by omega] at hk

theorem stepUpTo_39 : ∀ i, 10138 ≤ i → i < 15258 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15130
  · exact stepUpTo_38 i hlo h
  have hk := sBlock39 (i - 15130) (by omega)
  rwa [show 15130 + (i - 15130) = i by omega] at hk

theorem stepUpTo_40 : ∀ i, 10138 ≤ i → i < 15386 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15258
  · exact stepUpTo_39 i hlo h
  have hk := sBlock40 (i - 15258) (by omega)
  rwa [show 15258 + (i - 15258) = i by omega] at hk

theorem stepUpTo_41 : ∀ i, 10138 ≤ i → i < 15514 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15386
  · exact stepUpTo_40 i hlo h
  have hk := sBlock41 (i - 15386) (by omega)
  rwa [show 15386 + (i - 15386) = i by omega] at hk

theorem stepUpTo_42 : ∀ i, 10138 ≤ i → i < 15642 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15514
  · exact stepUpTo_41 i hlo h
  have hk := sBlock42 (i - 15514) (by omega)
  rwa [show 15514 + (i - 15514) = i by omega] at hk

theorem stepUpTo_43 : ∀ i, 10138 ≤ i → i < 15770 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15642
  · exact stepUpTo_42 i hlo h
  have hk := sBlock43 (i - 15642) (by omega)
  rwa [show 15642 + (i - 15642) = i by omega] at hk

theorem stepUpTo_44 : ∀ i, 10138 ≤ i → i < 15898 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15770
  · exact stepUpTo_43 i hlo h
  have hk := sBlock44 (i - 15770) (by omega)
  rwa [show 15770 + (i - 15770) = i by omega] at hk

theorem stepUpTo_45 : ∀ i, 10138 ≤ i → i < 16026 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15898
  · exact stepUpTo_44 i hlo h
  have hk := sBlock45 (i - 15898) (by omega)
  rwa [show 15898 + (i - 15898) = i by omega] at hk

theorem stepUpTo_46 : ∀ i, 10138 ≤ i → i < 16154 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16026
  · exact stepUpTo_45 i hlo h
  have hk := sBlock46 (i - 16026) (by omega)
  rwa [show 16026 + (i - 16026) = i by omega] at hk

theorem stepUpTo_47 : ∀ i, 10138 ≤ i → i < 16282 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16154
  · exact stepUpTo_46 i hlo h
  have hk := sBlock47 (i - 16154) (by omega)
  rwa [show 16154 + (i - 16154) = i by omega] at hk

theorem stepUpTo_48 : ∀ i, 10138 ≤ i → i < 16410 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16282
  · exact stepUpTo_47 i hlo h
  have hk := sBlock48 (i - 16282) (by omega)
  rwa [show 16282 + (i - 16282) = i by omega] at hk

theorem stepUpTo_49 : ∀ i, 10138 ≤ i → i < 16538 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16410
  · exact stepUpTo_48 i hlo h
  have hk := sBlock49 (i - 16410) (by omega)
  rwa [show 16410 + (i - 16410) = i by omega] at hk

theorem stepUpTo_50 : ∀ i, 10138 ≤ i → i < 16666 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16538
  · exact stepUpTo_49 i hlo h
  have hk := sBlock50 (i - 16538) (by omega)
  rwa [show 16538 + (i - 16538) = i by omega] at hk

theorem stepUpTo_51 : ∀ i, 10138 ≤ i → i < 16794 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16666
  · exact stepUpTo_50 i hlo h
  have hk := sBlock51 (i - 16666) (by omega)
  rwa [show 16666 + (i - 16666) = i by omega] at hk

theorem stepUpTo_52 : ∀ i, 10138 ≤ i → i < 16922 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16794
  · exact stepUpTo_51 i hlo h
  have hk := sBlock52 (i - 16794) (by omega)
  rwa [show 16794 + (i - 16794) = i by omega] at hk

theorem stepUpTo_53 : ∀ i, 10138 ≤ i → i < 17050 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16922
  · exact stepUpTo_52 i hlo h
  have hk := sBlock53 (i - 16922) (by omega)
  rwa [show 16922 + (i - 16922) = i by omega] at hk

theorem stepUpTo_54 : ∀ i, 10138 ≤ i → i < 17178 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17050
  · exact stepUpTo_53 i hlo h
  have hk := sBlock54 (i - 17050) (by omega)
  rwa [show 17050 + (i - 17050) = i by omega] at hk

theorem stepUpTo_55 : ∀ i, 10138 ≤ i → i < 17306 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17178
  · exact stepUpTo_54 i hlo h
  have hk := sBlock55 (i - 17178) (by omega)
  rwa [show 17178 + (i - 17178) = i by omega] at hk

theorem stepUpTo_56 : ∀ i, 10138 ≤ i → i < 17367 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17306
  · exact stepUpTo_55 i hlo h
  have hk := sBlock56 (i - 17306) (by omega)
  rwa [show 17306 + (i - 17306) = i by omega] at hk

/-- Check S3_21_167_t42: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 10138 17367 17366
    initUpTo_79 stepUpTo_56 (by decide) final_ok z hz

end UC85.W.C.S3_21_167_t42
