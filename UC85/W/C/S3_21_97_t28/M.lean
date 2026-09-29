import UC85.W.C.S3_21_97_t28.Tab
import UC85.W.C.S3_21_97_t28.I0
import UC85.W.C.S3_21_97_t28.I1
import UC85.W.C.S3_21_97_t28.I2
import UC85.W.C.S3_21_97_t28.I3
import UC85.W.C.S3_21_97_t28.I4
import UC85.W.C.S3_21_97_t28.I5
import UC85.W.C.S3_21_97_t28.I6
import UC85.W.C.S3_21_97_t28.I7
import UC85.W.C.S3_21_97_t28.S0
import UC85.W.C.S3_21_97_t28.S1
import UC85.W.C.S3_21_97_t28.S2
import UC85.W.C.S3_21_97_t28.S3
import UC85.W.C.S3_21_97_t28.S4
import UC85.W.C.S3_21_97_t28.S5
import UC85.W.C.S3_21_97_t28.S6
import UC85.W.C.S3_21_97_t28.S7
import UC85.W.C.S3_21_97_t28.S8
import UC85.W.C.S3_21_97_t28.S9
import UC85.W.C.S3_21_97_t28.S10
import UC85.W.C.S3_21_97_t28.S11
import UC85.W.C.S3_21_97_t28.S12
import UC85.W.C.S3_21_97_t28.S13
import UC85.W.C.S3_21_97_t28.S14
import UC85.W.C.S3_21_97_t28.S15
import UC85.W.C.S3_21_97_t28.S16
import UC85.W.C.S3_21_97_t28.S17
import UC85.W.C.S3_21_97_t28.S18
import UC85.W.C.S3_21_97_t28.S19
import UC85.W.C.S3_21_97_t28.S20
import UC85.W.C.S3_21_97_t28.S21
import UC85.W.C.S3_21_97_t28.S22
import UC85.W.C.S3_21_97_t28.S23
import UC85.W.C.S3_21_97_t28.S24
import UC85.W.C.S3_21_97_t28.S25
import UC85.W.C.S3_21_97_t28.S26
import UC85.W.C.S3_21_97_t28.S27
import UC85.W.C.S3_21_97_t28.S28
import UC85.W.C.S3_21_97_t28.S29
import UC85.W.C.S3_21_97_t28.S30
import UC85.W.C.S3_21_97_t28.S31
import UC85.W.C.S3_21_97_t28.S32
import UC85.W.C.S3_21_97_t28.S33
import UC85.W.C.S3_21_97_t28.S34
import UC85.W.C.S3_21_97_t28.S35
import UC85.W.C.S3_21_97_t28.S36
import UC85.W.C.S3_21_97_t28.S37
import UC85.W.C.S3_21_97_t28.S38
import UC85.W.C.S3_21_97_t28.S39
import UC85.W.C.S3_21_97_t28.S40
import UC85.W.C.S3_21_97_t28.S41
import UC85.W.C.S3_21_97_t28.S42
import UC85.W.C.S3_21_97_t28.S43
import UC85.W.C.S3_21_97_t28.S44
import UC85.W.C.S3_21_97_t28.S45
import UC85.W.C.S3_21_97_t28.S46
import UC85.W.C.S3_21_97_t28.S47
import UC85.W.C.S3_21_97_t28.S48
import UC85.W.C.S3_21_97_t28.S49
import UC85.W.C.S3_21_97_t28.S50
import UC85.W.C.S3_21_97_t28.S51
import UC85.W.C.S3_21_97_t28.S52
import UC85.W.C.S3_21_97_t28.S53
import UC85.W.C.S3_21_97_t28.S54
import UC85.W.C.S3_21_97_t28.S55
import UC85.W.C.S3_21_97_t28.S56
import UC85.W.C.S3_21_97_t28.S57
import UC85.W.C.S3_21_97_t28.S58
import UC85.W.C.S3_21_97_t28.S59
import UC85.W.C.S3_21_97_t28.S60
import UC85.W.C.S3_21_97_t28.S61
import UC85.W.C.S3_21_97_t28.S62
import UC85.W.C.S3_21_97_t28.S63
import UC85.W.C.S3_21_97_t28.S64
import UC85.W.C.S3_21_97_t28.S65
import UC85.W.C.S3_21_97_t28.S66
import UC85.W.C.S3_21_97_t28.S67
import UC85.W.C.S3_21_97_t28.S68
import UC85.W.C.S3_21_97_t28.S69
import UC85.W.C.S3_21_97_t28.S70
import UC85.W.C.S3_21_97_t28.S71
import UC85.W.C.S3_21_97_t28.S72
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_97_t28
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

theorem initUpTo_79 : ∀ i, i < 10240 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10112
  · exact initUpTo_78 i h
  have hk := oBlock79 (i - 10112) (by omega)
  rwa [show 10112 + (i - 10112) = i by omega] at hk

theorem initUpTo_80 : ∀ i, i < 10368 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10240
  · exact initUpTo_79 i h
  have hk := oBlock80 (i - 10240) (by omega)
  rwa [show 10240 + (i - 10240) = i by omega] at hk

theorem initUpTo_81 : ∀ i, i < 10496 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10368
  · exact initUpTo_80 i h
  have hk := oBlock81 (i - 10368) (by omega)
  rwa [show 10368 + (i - 10368) = i by omega] at hk

theorem initUpTo_82 : ∀ i, i < 10624 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10496
  · exact initUpTo_81 i h
  have hk := oBlock82 (i - 10496) (by omega)
  rwa [show 10496 + (i - 10496) = i by omega] at hk

theorem initUpTo_83 : ∀ i, i < 10752 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10624
  · exact initUpTo_82 i h
  have hk := oBlock83 (i - 10624) (by omega)
  rwa [show 10624 + (i - 10624) = i by omega] at hk

theorem initUpTo_84 : ∀ i, i < 10880 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10752
  · exact initUpTo_83 i h
  have hk := oBlock84 (i - 10752) (by omega)
  rwa [show 10752 + (i - 10752) = i by omega] at hk

theorem initUpTo_85 : ∀ i, i < 11008 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 10880
  · exact initUpTo_84 i h
  have hk := oBlock85 (i - 10880) (by omega)
  rwa [show 10880 + (i - 10880) = i by omega] at hk

theorem initUpTo_86 : ∀ i, i < 11136 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11008
  · exact initUpTo_85 i h
  have hk := oBlock86 (i - 11008) (by omega)
  rwa [show 11008 + (i - 11008) = i by omega] at hk

theorem initUpTo_87 : ∀ i, i < 11264 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11136
  · exact initUpTo_86 i h
  have hk := oBlock87 (i - 11136) (by omega)
  rwa [show 11136 + (i - 11136) = i by omega] at hk

theorem initUpTo_88 : ∀ i, i < 11392 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11264
  · exact initUpTo_87 i h
  have hk := oBlock88 (i - 11264) (by omega)
  rwa [show 11264 + (i - 11264) = i by omega] at hk

theorem initUpTo_89 : ∀ i, i < 11520 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11392
  · exact initUpTo_88 i h
  have hk := oBlock89 (i - 11392) (by omega)
  rwa [show 11392 + (i - 11392) = i by omega] at hk

theorem initUpTo_90 : ∀ i, i < 11648 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11520
  · exact initUpTo_89 i h
  have hk := oBlock90 (i - 11520) (by omega)
  rwa [show 11520 + (i - 11520) = i by omega] at hk

theorem initUpTo_91 : ∀ i, i < 11776 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11648
  · exact initUpTo_90 i h
  have hk := oBlock91 (i - 11648) (by omega)
  rwa [show 11648 + (i - 11648) = i by omega] at hk

theorem initUpTo_92 : ∀ i, i < 11904 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11776
  · exact initUpTo_91 i h
  have hk := oBlock92 (i - 11776) (by omega)
  rwa [show 11776 + (i - 11776) = i by omega] at hk

theorem initUpTo_93 : ∀ i, i < 12032 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11904
  · exact initUpTo_92 i h
  have hk := oBlock93 (i - 11904) (by omega)
  rwa [show 11904 + (i - 11904) = i by omega] at hk

theorem initUpTo_94 : ∀ i, i < 12160 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12032
  · exact initUpTo_93 i h
  have hk := oBlock94 (i - 12032) (by omega)
  rwa [show 12032 + (i - 12032) = i by omega] at hk

theorem initUpTo_95 : ∀ i, i < 12288 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12160
  · exact initUpTo_94 i h
  have hk := oBlock95 (i - 12160) (by omega)
  rwa [show 12160 + (i - 12160) = i by omega] at hk

theorem initUpTo_96 : ∀ i, i < 12416 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12288
  · exact initUpTo_95 i h
  have hk := oBlock96 (i - 12288) (by omega)
  rwa [show 12288 + (i - 12288) = i by omega] at hk

theorem initUpTo_97 : ∀ i, i < 12544 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12416
  · exact initUpTo_96 i h
  have hk := oBlock97 (i - 12416) (by omega)
  rwa [show 12416 + (i - 12416) = i by omega] at hk

theorem initUpTo_98 : ∀ i, i < 12672 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12544
  · exact initUpTo_97 i h
  have hk := oBlock98 (i - 12544) (by omega)
  rwa [show 12544 + (i - 12544) = i by omega] at hk

theorem initUpTo_99 : ∀ i, i < 12800 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12672
  · exact initUpTo_98 i h
  have hk := oBlock99 (i - 12672) (by omega)
  rwa [show 12672 + (i - 12672) = i by omega] at hk

theorem initUpTo_100 : ∀ i, i < 12928 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12800
  · exact initUpTo_99 i h
  have hk := oBlock100 (i - 12800) (by omega)
  rwa [show 12800 + (i - 12800) = i by omega] at hk

theorem initUpTo_101 : ∀ i, i < 13056 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 12928
  · exact initUpTo_100 i h
  have hk := oBlock101 (i - 12928) (by omega)
  rwa [show 12928 + (i - 12928) = i by omega] at hk

theorem initUpTo_102 : ∀ i, i < 13184 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13056
  · exact initUpTo_101 i h
  have hk := oBlock102 (i - 13056) (by omega)
  rwa [show 13056 + (i - 13056) = i by omega] at hk

theorem initUpTo_103 : ∀ i, i < 13312 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13184
  · exact initUpTo_102 i h
  have hk := oBlock103 (i - 13184) (by omega)
  rwa [show 13184 + (i - 13184) = i by omega] at hk

theorem initUpTo_104 : ∀ i, i < 13440 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13312
  · exact initUpTo_103 i h
  have hk := oBlock104 (i - 13312) (by omega)
  rwa [show 13312 + (i - 13312) = i by omega] at hk

theorem initUpTo_105 : ∀ i, i < 13568 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13440
  · exact initUpTo_104 i h
  have hk := oBlock105 (i - 13440) (by omega)
  rwa [show 13440 + (i - 13440) = i by omega] at hk

theorem initUpTo_106 : ∀ i, i < 13696 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13568
  · exact initUpTo_105 i h
  have hk := oBlock106 (i - 13568) (by omega)
  rwa [show 13568 + (i - 13568) = i by omega] at hk

theorem initUpTo_107 : ∀ i, i < 13824 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13696
  · exact initUpTo_106 i h
  have hk := oBlock107 (i - 13696) (by omega)
  rwa [show 13696 + (i - 13696) = i by omega] at hk

theorem initUpTo_108 : ∀ i, i < 13952 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13824
  · exact initUpTo_107 i h
  have hk := oBlock108 (i - 13824) (by omega)
  rwa [show 13824 + (i - 13824) = i by omega] at hk

theorem initUpTo_109 : ∀ i, i < 14080 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 13952
  · exact initUpTo_108 i h
  have hk := oBlock109 (i - 13952) (by omega)
  rwa [show 13952 + (i - 13952) = i by omega] at hk

theorem initUpTo_110 : ∀ i, i < 14208 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14080
  · exact initUpTo_109 i h
  have hk := oBlock110 (i - 14080) (by omega)
  rwa [show 14080 + (i - 14080) = i by omega] at hk

theorem initUpTo_111 : ∀ i, i < 14336 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14208
  · exact initUpTo_110 i h
  have hk := oBlock111 (i - 14208) (by omega)
  rwa [show 14208 + (i - 14208) = i by omega] at hk

theorem initUpTo_112 : ∀ i, i < 14464 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14336
  · exact initUpTo_111 i h
  have hk := oBlock112 (i - 14336) (by omega)
  rwa [show 14336 + (i - 14336) = i by omega] at hk

theorem initUpTo_113 : ∀ i, i < 14592 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14464
  · exact initUpTo_112 i h
  have hk := oBlock113 (i - 14464) (by omega)
  rwa [show 14464 + (i - 14464) = i by omega] at hk

theorem initUpTo_114 : ∀ i, i < 14720 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14592
  · exact initUpTo_113 i h
  have hk := oBlock114 (i - 14592) (by omega)
  rwa [show 14592 + (i - 14592) = i by omega] at hk

theorem initUpTo_115 : ∀ i, i < 14848 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14720
  · exact initUpTo_114 i h
  have hk := oBlock115 (i - 14720) (by omega)
  rwa [show 14720 + (i - 14720) = i by omega] at hk

theorem initUpTo_116 : ∀ i, i < 14976 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14848
  · exact initUpTo_115 i h
  have hk := oBlock116 (i - 14848) (by omega)
  rwa [show 14848 + (i - 14848) = i by omega] at hk

theorem initUpTo_117 : ∀ i, i < 15074 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 14976
  · exact initUpTo_116 i h
  have hk := oBlock117 (i - 14976) (by omega)
  rwa [show 14976 + (i - 14976) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 15074 ≤ i → i < 15202 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 15074) (by omega)
  rwa [show 15074 + (i - 15074) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 15074 ≤ i → i < 15330 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15202
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 15202) (by omega)
  rwa [show 15202 + (i - 15202) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 15074 ≤ i → i < 15458 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15330
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 15330) (by omega)
  rwa [show 15330 + (i - 15330) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 15074 ≤ i → i < 15586 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15458
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 15458) (by omega)
  rwa [show 15458 + (i - 15458) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 15074 ≤ i → i < 15714 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15586
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 15586) (by omega)
  rwa [show 15586 + (i - 15586) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 15074 ≤ i → i < 15842 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15714
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 15714) (by omega)
  rwa [show 15714 + (i - 15714) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 15074 ≤ i → i < 15970 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15842
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 15842) (by omega)
  rwa [show 15842 + (i - 15842) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 15074 ≤ i → i < 16098 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15970
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 15970) (by omega)
  rwa [show 15970 + (i - 15970) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 15074 ≤ i → i < 16226 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16098
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 16098) (by omega)
  rwa [show 16098 + (i - 16098) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 15074 ≤ i → i < 16354 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16226
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 16226) (by omega)
  rwa [show 16226 + (i - 16226) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 15074 ≤ i → i < 16482 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16354
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 16354) (by omega)
  rwa [show 16354 + (i - 16354) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 15074 ≤ i → i < 16610 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16482
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 16482) (by omega)
  rwa [show 16482 + (i - 16482) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 15074 ≤ i → i < 16738 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16610
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 16610) (by omega)
  rwa [show 16610 + (i - 16610) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 15074 ≤ i → i < 16866 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16738
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 16738) (by omega)
  rwa [show 16738 + (i - 16738) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 15074 ≤ i → i < 16994 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16866
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 16866) (by omega)
  rwa [show 16866 + (i - 16866) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 15074 ≤ i → i < 17122 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16994
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 16994) (by omega)
  rwa [show 16994 + (i - 16994) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 15074 ≤ i → i < 17250 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17122
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 17122) (by omega)
  rwa [show 17122 + (i - 17122) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 15074 ≤ i → i < 17378 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17250
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 17250) (by omega)
  rwa [show 17250 + (i - 17250) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 15074 ≤ i → i < 17506 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17378
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 17378) (by omega)
  rwa [show 17378 + (i - 17378) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 15074 ≤ i → i < 17634 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17506
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 17506) (by omega)
  rwa [show 17506 + (i - 17506) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 15074 ≤ i → i < 17762 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17634
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 17634) (by omega)
  rwa [show 17634 + (i - 17634) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 15074 ≤ i → i < 17890 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17762
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 17762) (by omega)
  rwa [show 17762 + (i - 17762) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 15074 ≤ i → i < 18018 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17890
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 17890) (by omega)
  rwa [show 17890 + (i - 17890) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 15074 ≤ i → i < 18146 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18018
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 18018) (by omega)
  rwa [show 18018 + (i - 18018) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 15074 ≤ i → i < 18274 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18146
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 18146) (by omega)
  rwa [show 18146 + (i - 18146) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 15074 ≤ i → i < 18402 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18274
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 18274) (by omega)
  rwa [show 18274 + (i - 18274) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 15074 ≤ i → i < 18530 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18402
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 18402) (by omega)
  rwa [show 18402 + (i - 18402) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 15074 ≤ i → i < 18658 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18530
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 18530) (by omega)
  rwa [show 18530 + (i - 18530) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 15074 ≤ i → i < 18786 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18658
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 18658) (by omega)
  rwa [show 18658 + (i - 18658) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 15074 ≤ i → i < 18914 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18786
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 18786) (by omega)
  rwa [show 18786 + (i - 18786) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 15074 ≤ i → i < 19042 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18914
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 18914) (by omega)
  rwa [show 18914 + (i - 18914) = i by omega] at hk

theorem stepUpTo_31 : ∀ i, 15074 ≤ i → i < 19170 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19042
  · exact stepUpTo_30 i hlo h
  have hk := sBlock31 (i - 19042) (by omega)
  rwa [show 19042 + (i - 19042) = i by omega] at hk

theorem stepUpTo_32 : ∀ i, 15074 ≤ i → i < 19298 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19170
  · exact stepUpTo_31 i hlo h
  have hk := sBlock32 (i - 19170) (by omega)
  rwa [show 19170 + (i - 19170) = i by omega] at hk

theorem stepUpTo_33 : ∀ i, 15074 ≤ i → i < 19426 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19298
  · exact stepUpTo_32 i hlo h
  have hk := sBlock33 (i - 19298) (by omega)
  rwa [show 19298 + (i - 19298) = i by omega] at hk

theorem stepUpTo_34 : ∀ i, 15074 ≤ i → i < 19554 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19426
  · exact stepUpTo_33 i hlo h
  have hk := sBlock34 (i - 19426) (by omega)
  rwa [show 19426 + (i - 19426) = i by omega] at hk

theorem stepUpTo_35 : ∀ i, 15074 ≤ i → i < 19682 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19554
  · exact stepUpTo_34 i hlo h
  have hk := sBlock35 (i - 19554) (by omega)
  rwa [show 19554 + (i - 19554) = i by omega] at hk

theorem stepUpTo_36 : ∀ i, 15074 ≤ i → i < 19810 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19682
  · exact stepUpTo_35 i hlo h
  have hk := sBlock36 (i - 19682) (by omega)
  rwa [show 19682 + (i - 19682) = i by omega] at hk

theorem stepUpTo_37 : ∀ i, 15074 ≤ i → i < 19938 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19810
  · exact stepUpTo_36 i hlo h
  have hk := sBlock37 (i - 19810) (by omega)
  rwa [show 19810 + (i - 19810) = i by omega] at hk

theorem stepUpTo_38 : ∀ i, 15074 ≤ i → i < 20066 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19938
  · exact stepUpTo_37 i hlo h
  have hk := sBlock38 (i - 19938) (by omega)
  rwa [show 19938 + (i - 19938) = i by omega] at hk

theorem stepUpTo_39 : ∀ i, 15074 ≤ i → i < 20194 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20066
  · exact stepUpTo_38 i hlo h
  have hk := sBlock39 (i - 20066) (by omega)
  rwa [show 20066 + (i - 20066) = i by omega] at hk

theorem stepUpTo_40 : ∀ i, 15074 ≤ i → i < 20322 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20194
  · exact stepUpTo_39 i hlo h
  have hk := sBlock40 (i - 20194) (by omega)
  rwa [show 20194 + (i - 20194) = i by omega] at hk

theorem stepUpTo_41 : ∀ i, 15074 ≤ i → i < 20450 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20322
  · exact stepUpTo_40 i hlo h
  have hk := sBlock41 (i - 20322) (by omega)
  rwa [show 20322 + (i - 20322) = i by omega] at hk

theorem stepUpTo_42 : ∀ i, 15074 ≤ i → i < 20578 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20450
  · exact stepUpTo_41 i hlo h
  have hk := sBlock42 (i - 20450) (by omega)
  rwa [show 20450 + (i - 20450) = i by omega] at hk

theorem stepUpTo_43 : ∀ i, 15074 ≤ i → i < 20706 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20578
  · exact stepUpTo_42 i hlo h
  have hk := sBlock43 (i - 20578) (by omega)
  rwa [show 20578 + (i - 20578) = i by omega] at hk

theorem stepUpTo_44 : ∀ i, 15074 ≤ i → i < 20834 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20706
  · exact stepUpTo_43 i hlo h
  have hk := sBlock44 (i - 20706) (by omega)
  rwa [show 20706 + (i - 20706) = i by omega] at hk

theorem stepUpTo_45 : ∀ i, 15074 ≤ i → i < 20962 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20834
  · exact stepUpTo_44 i hlo h
  have hk := sBlock45 (i - 20834) (by omega)
  rwa [show 20834 + (i - 20834) = i by omega] at hk

theorem stepUpTo_46 : ∀ i, 15074 ≤ i → i < 21090 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20962
  · exact stepUpTo_45 i hlo h
  have hk := sBlock46 (i - 20962) (by omega)
  rwa [show 20962 + (i - 20962) = i by omega] at hk

theorem stepUpTo_47 : ∀ i, 15074 ≤ i → i < 21218 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21090
  · exact stepUpTo_46 i hlo h
  have hk := sBlock47 (i - 21090) (by omega)
  rwa [show 21090 + (i - 21090) = i by omega] at hk

theorem stepUpTo_48 : ∀ i, 15074 ≤ i → i < 21346 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21218
  · exact stepUpTo_47 i hlo h
  have hk := sBlock48 (i - 21218) (by omega)
  rwa [show 21218 + (i - 21218) = i by omega] at hk

theorem stepUpTo_49 : ∀ i, 15074 ≤ i → i < 21474 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21346
  · exact stepUpTo_48 i hlo h
  have hk := sBlock49 (i - 21346) (by omega)
  rwa [show 21346 + (i - 21346) = i by omega] at hk

theorem stepUpTo_50 : ∀ i, 15074 ≤ i → i < 21602 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21474
  · exact stepUpTo_49 i hlo h
  have hk := sBlock50 (i - 21474) (by omega)
  rwa [show 21474 + (i - 21474) = i by omega] at hk

theorem stepUpTo_51 : ∀ i, 15074 ≤ i → i < 21730 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21602
  · exact stepUpTo_50 i hlo h
  have hk := sBlock51 (i - 21602) (by omega)
  rwa [show 21602 + (i - 21602) = i by omega] at hk

theorem stepUpTo_52 : ∀ i, 15074 ≤ i → i < 21858 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21730
  · exact stepUpTo_51 i hlo h
  have hk := sBlock52 (i - 21730) (by omega)
  rwa [show 21730 + (i - 21730) = i by omega] at hk

theorem stepUpTo_53 : ∀ i, 15074 ≤ i → i < 21986 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21858
  · exact stepUpTo_52 i hlo h
  have hk := sBlock53 (i - 21858) (by omega)
  rwa [show 21858 + (i - 21858) = i by omega] at hk

theorem stepUpTo_54 : ∀ i, 15074 ≤ i → i < 22114 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21986
  · exact stepUpTo_53 i hlo h
  have hk := sBlock54 (i - 21986) (by omega)
  rwa [show 21986 + (i - 21986) = i by omega] at hk

theorem stepUpTo_55 : ∀ i, 15074 ≤ i → i < 22242 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22114
  · exact stepUpTo_54 i hlo h
  have hk := sBlock55 (i - 22114) (by omega)
  rwa [show 22114 + (i - 22114) = i by omega] at hk

theorem stepUpTo_56 : ∀ i, 15074 ≤ i → i < 22370 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22242
  · exact stepUpTo_55 i hlo h
  have hk := sBlock56 (i - 22242) (by omega)
  rwa [show 22242 + (i - 22242) = i by omega] at hk

theorem stepUpTo_57 : ∀ i, 15074 ≤ i → i < 22498 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22370
  · exact stepUpTo_56 i hlo h
  have hk := sBlock57 (i - 22370) (by omega)
  rwa [show 22370 + (i - 22370) = i by omega] at hk

theorem stepUpTo_58 : ∀ i, 15074 ≤ i → i < 22626 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22498
  · exact stepUpTo_57 i hlo h
  have hk := sBlock58 (i - 22498) (by omega)
  rwa [show 22498 + (i - 22498) = i by omega] at hk

theorem stepUpTo_59 : ∀ i, 15074 ≤ i → i < 22754 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22626
  · exact stepUpTo_58 i hlo h
  have hk := sBlock59 (i - 22626) (by omega)
  rwa [show 22626 + (i - 22626) = i by omega] at hk

theorem stepUpTo_60 : ∀ i, 15074 ≤ i → i < 22882 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22754
  · exact stepUpTo_59 i hlo h
  have hk := sBlock60 (i - 22754) (by omega)
  rwa [show 22754 + (i - 22754) = i by omega] at hk

theorem stepUpTo_61 : ∀ i, 15074 ≤ i → i < 23010 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22882
  · exact stepUpTo_60 i hlo h
  have hk := sBlock61 (i - 22882) (by omega)
  rwa [show 22882 + (i - 22882) = i by omega] at hk

theorem stepUpTo_62 : ∀ i, 15074 ≤ i → i < 23138 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23010
  · exact stepUpTo_61 i hlo h
  have hk := sBlock62 (i - 23010) (by omega)
  rwa [show 23010 + (i - 23010) = i by omega] at hk

theorem stepUpTo_63 : ∀ i, 15074 ≤ i → i < 23266 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23138
  · exact stepUpTo_62 i hlo h
  have hk := sBlock63 (i - 23138) (by omega)
  rwa [show 23138 + (i - 23138) = i by omega] at hk

theorem stepUpTo_64 : ∀ i, 15074 ≤ i → i < 23394 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23266
  · exact stepUpTo_63 i hlo h
  have hk := sBlock64 (i - 23266) (by omega)
  rwa [show 23266 + (i - 23266) = i by omega] at hk

theorem stepUpTo_65 : ∀ i, 15074 ≤ i → i < 23522 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23394
  · exact stepUpTo_64 i hlo h
  have hk := sBlock65 (i - 23394) (by omega)
  rwa [show 23394 + (i - 23394) = i by omega] at hk

theorem stepUpTo_66 : ∀ i, 15074 ≤ i → i < 23650 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23522
  · exact stepUpTo_65 i hlo h
  have hk := sBlock66 (i - 23522) (by omega)
  rwa [show 23522 + (i - 23522) = i by omega] at hk

theorem stepUpTo_67 : ∀ i, 15074 ≤ i → i < 23778 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23650
  · exact stepUpTo_66 i hlo h
  have hk := sBlock67 (i - 23650) (by omega)
  rwa [show 23650 + (i - 23650) = i by omega] at hk

theorem stepUpTo_68 : ∀ i, 15074 ≤ i → i < 23906 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23778
  · exact stepUpTo_67 i hlo h
  have hk := sBlock68 (i - 23778) (by omega)
  rwa [show 23778 + (i - 23778) = i by omega] at hk

theorem stepUpTo_69 : ∀ i, 15074 ≤ i → i < 24034 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 23906
  · exact stepUpTo_68 i hlo h
  have hk := sBlock69 (i - 23906) (by omega)
  rwa [show 23906 + (i - 23906) = i by omega] at hk

theorem stepUpTo_70 : ∀ i, 15074 ≤ i → i < 24162 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 24034
  · exact stepUpTo_69 i hlo h
  have hk := sBlock70 (i - 24034) (by omega)
  rwa [show 24034 + (i - 24034) = i by omega] at hk

theorem stepUpTo_71 : ∀ i, 15074 ≤ i → i < 24290 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 24162
  · exact stepUpTo_70 i hlo h
  have hk := sBlock71 (i - 24162) (by omega)
  rwa [show 24162 + (i - 24162) = i by omega] at hk

theorem stepUpTo_72 : ∀ i, 15074 ≤ i → i < 24417 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 24290
  · exact stepUpTo_71 i hlo h
  have hk := sBlock72 (i - 24290) (by omega)
  rwa [show 24290 + (i - 24290) = i by omega] at hk

/-- Check S3_21_97_t28: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 15074 24417 24416
    initUpTo_117 stepUpTo_72 (by decide) final_ok z hz

end UC85.W.C.S3_21_97_t28
