import UC85.W.C.S3_21_137_t36.Tab
import UC85.W.C.S3_21_137_t36.I0
import UC85.W.C.S3_21_137_t36.I1
import UC85.W.C.S3_21_137_t36.I2
import UC85.W.C.S3_21_137_t36.I3
import UC85.W.C.S3_21_137_t36.I4
import UC85.W.C.S3_21_137_t36.I5
import UC85.W.C.S3_21_137_t36.S0
import UC85.W.C.S3_21_137_t36.S1
import UC85.W.C.S3_21_137_t36.S2
import UC85.W.C.S3_21_137_t36.S3
import UC85.W.C.S3_21_137_t36.S4
import UC85.W.C.S3_21_137_t36.S5
import UC85.W.C.S3_21_137_t36.S6
import UC85.W.C.S3_21_137_t36.S7
import UC85.W.C.S3_21_137_t36.S8
import UC85.W.C.S3_21_137_t36.S9
import UC85.W.C.S3_21_137_t36.S10
import UC85.W.C.S3_21_137_t36.S11
import UC85.W.C.S3_21_137_t36.S12
import UC85.W.C.S3_21_137_t36.S13
import UC85.W.C.S3_21_137_t36.S14
import UC85.W.C.S3_21_137_t36.S15
import UC85.W.C.S3_21_137_t36.S16
import UC85.W.C.S3_21_137_t36.S17
import UC85.W.C.S3_21_137_t36.S18
import UC85.W.C.S3_21_137_t36.S19
import UC85.W.C.S3_21_137_t36.S20
import UC85.W.C.S3_21_137_t36.S21
import UC85.W.C.S3_21_137_t36.S22
import UC85.W.C.S3_21_137_t36.S23
import UC85.W.C.S3_21_137_t36.S24
import UC85.W.C.S3_21_137_t36.S25
import UC85.W.C.S3_21_137_t36.S26
import UC85.W.C.S3_21_137_t36.S27
import UC85.W.C.S3_21_137_t36.S28
import UC85.W.C.S3_21_137_t36.S29
import UC85.W.C.S3_21_137_t36.S30
import UC85.W.C.S3_21_137_t36.S31
import UC85.W.C.S3_21_137_t36.S32
import UC85.W.C.S3_21_137_t36.S33
import UC85.W.C.S3_21_137_t36.S34
import UC85.W.C.S3_21_137_t36.S35
import UC85.W.C.S3_21_137_t36.S36
import UC85.W.C.S3_21_137_t36.S37
import UC85.W.C.S3_21_137_t36.S38
import UC85.W.C.S3_21_137_t36.S39
import UC85.W.C.S3_21_137_t36.S40
import UC85.W.C.S3_21_137_t36.S41
import UC85.W.C.S3_21_137_t36.S42
import UC85.W.C.S3_21_137_t36.S43
import UC85.W.C.S3_21_137_t36.S44
import UC85.W.C.S3_21_137_t36.S45
import UC85.W.C.S3_21_137_t36.S46
import UC85.W.C.S3_21_137_t36.S47
import UC85.W.C.S3_21_137_t36.S48
import UC85.W.C.S3_21_137_t36.S49
import UC85.W.C.S3_21_137_t36.S50
import UC85.W.C.S3_21_137_t36.S51
import UC85.W.C.S3_21_137_t36.S52
import UC85.W.C.S3_21_137_t36.S53
import UC85.W.C.S3_21_137_t36.S54
import UC85.W.C.S3_21_137_t36.S55
import UC85.W.C.S3_21_137_t36.S56
import UC85.W.C.S3_21_137_t36.S57
import UC85.W.C.S3_21_137_t36.S58
import UC85.W.C.S3_21_137_t36.S59
import UC85.W.C.S3_21_137_t36.S60
import UC85.W.C.S3_21_137_t36.S61
import UC85.W.C.S3_21_137_t36.S62
import UC85.W.C.S3_21_137_t36.S63
import UC85.W.C.S3_21_137_t36.S64
import UC85.W.C.S3_21_137_t36.S65
import UC85.W.C.S3_21_137_t36.S66
import UC85.W.C.S3_21_137_t36.S67
import UC85.W.C.S3_21_137_t36.S68
import UC85.W.C.S3_21_137_t36.S69
import UC85.W.C.S3_21_137_t36.S70
import UC85.W.C.S3_21_137_t36.S71
import UC85.W.C.S3_21_137_t36.S72
import UC85.W.C.S3_21_137_t36.S73
import UC85.W.C.S3_21_137_t36.S74
import UC85.W.C.S3_21_137_t36.S75
import UC85.W.C.S3_21_137_t36.S76
import UC85.W.C.S3_21_137_t36.S77
import UC85.W.C.S3_21_137_t36.S78
import UC85.W.C.S3_21_137_t36.S79
import UC85.W.C.S3_21_137_t36.S80
import UC85.W.C.S3_21_137_t36.S81
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_137_t36
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

theorem initUpTo_93 : ∀ i, i < 11954 → E.originOK (origin i) (rupClauses i) = true := by
  intro i hi
  by_cases h : i < 11904
  · exact initUpTo_92 i h
  have hk := oBlock93 (i - 11904) (by omega)
  rwa [show 11904 + (i - 11904) = i by omega] at hk

theorem stepUpTo_0 : ∀ i, 11954 ≤ i → i < 12082 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  have hk := sBlock0 (i - 11954) (by omega)
  rwa [show 11954 + (i - 11954) = i by omega] at hk

theorem stepUpTo_1 : ∀ i, 11954 ≤ i → i < 12210 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12082
  · exact stepUpTo_0 i hlo h
  have hk := sBlock1 (i - 12082) (by omega)
  rwa [show 12082 + (i - 12082) = i by omega] at hk

theorem stepUpTo_2 : ∀ i, 11954 ≤ i → i < 12338 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12210
  · exact stepUpTo_1 i hlo h
  have hk := sBlock2 (i - 12210) (by omega)
  rwa [show 12210 + (i - 12210) = i by omega] at hk

theorem stepUpTo_3 : ∀ i, 11954 ≤ i → i < 12466 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12338
  · exact stepUpTo_2 i hlo h
  have hk := sBlock3 (i - 12338) (by omega)
  rwa [show 12338 + (i - 12338) = i by omega] at hk

theorem stepUpTo_4 : ∀ i, 11954 ≤ i → i < 12594 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12466
  · exact stepUpTo_3 i hlo h
  have hk := sBlock4 (i - 12466) (by omega)
  rwa [show 12466 + (i - 12466) = i by omega] at hk

theorem stepUpTo_5 : ∀ i, 11954 ≤ i → i < 12722 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12594
  · exact stepUpTo_4 i hlo h
  have hk := sBlock5 (i - 12594) (by omega)
  rwa [show 12594 + (i - 12594) = i by omega] at hk

theorem stepUpTo_6 : ∀ i, 11954 ≤ i → i < 12850 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12722
  · exact stepUpTo_5 i hlo h
  have hk := sBlock6 (i - 12722) (by omega)
  rwa [show 12722 + (i - 12722) = i by omega] at hk

theorem stepUpTo_7 : ∀ i, 11954 ≤ i → i < 12978 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12850
  · exact stepUpTo_6 i hlo h
  have hk := sBlock7 (i - 12850) (by omega)
  rwa [show 12850 + (i - 12850) = i by omega] at hk

theorem stepUpTo_8 : ∀ i, 11954 ≤ i → i < 13106 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 12978
  · exact stepUpTo_7 i hlo h
  have hk := sBlock8 (i - 12978) (by omega)
  rwa [show 12978 + (i - 12978) = i by omega] at hk

theorem stepUpTo_9 : ∀ i, 11954 ≤ i → i < 13234 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13106
  · exact stepUpTo_8 i hlo h
  have hk := sBlock9 (i - 13106) (by omega)
  rwa [show 13106 + (i - 13106) = i by omega] at hk

theorem stepUpTo_10 : ∀ i, 11954 ≤ i → i < 13362 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13234
  · exact stepUpTo_9 i hlo h
  have hk := sBlock10 (i - 13234) (by omega)
  rwa [show 13234 + (i - 13234) = i by omega] at hk

theorem stepUpTo_11 : ∀ i, 11954 ≤ i → i < 13490 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13362
  · exact stepUpTo_10 i hlo h
  have hk := sBlock11 (i - 13362) (by omega)
  rwa [show 13362 + (i - 13362) = i by omega] at hk

theorem stepUpTo_12 : ∀ i, 11954 ≤ i → i < 13618 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13490
  · exact stepUpTo_11 i hlo h
  have hk := sBlock12 (i - 13490) (by omega)
  rwa [show 13490 + (i - 13490) = i by omega] at hk

theorem stepUpTo_13 : ∀ i, 11954 ≤ i → i < 13746 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13618
  · exact stepUpTo_12 i hlo h
  have hk := sBlock13 (i - 13618) (by omega)
  rwa [show 13618 + (i - 13618) = i by omega] at hk

theorem stepUpTo_14 : ∀ i, 11954 ≤ i → i < 13874 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13746
  · exact stepUpTo_13 i hlo h
  have hk := sBlock14 (i - 13746) (by omega)
  rwa [show 13746 + (i - 13746) = i by omega] at hk

theorem stepUpTo_15 : ∀ i, 11954 ≤ i → i < 14002 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 13874
  · exact stepUpTo_14 i hlo h
  have hk := sBlock15 (i - 13874) (by omega)
  rwa [show 13874 + (i - 13874) = i by omega] at hk

theorem stepUpTo_16 : ∀ i, 11954 ≤ i → i < 14130 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14002
  · exact stepUpTo_15 i hlo h
  have hk := sBlock16 (i - 14002) (by omega)
  rwa [show 14002 + (i - 14002) = i by omega] at hk

theorem stepUpTo_17 : ∀ i, 11954 ≤ i → i < 14258 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14130
  · exact stepUpTo_16 i hlo h
  have hk := sBlock17 (i - 14130) (by omega)
  rwa [show 14130 + (i - 14130) = i by omega] at hk

theorem stepUpTo_18 : ∀ i, 11954 ≤ i → i < 14386 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14258
  · exact stepUpTo_17 i hlo h
  have hk := sBlock18 (i - 14258) (by omega)
  rwa [show 14258 + (i - 14258) = i by omega] at hk

theorem stepUpTo_19 : ∀ i, 11954 ≤ i → i < 14514 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14386
  · exact stepUpTo_18 i hlo h
  have hk := sBlock19 (i - 14386) (by omega)
  rwa [show 14386 + (i - 14386) = i by omega] at hk

theorem stepUpTo_20 : ∀ i, 11954 ≤ i → i < 14642 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14514
  · exact stepUpTo_19 i hlo h
  have hk := sBlock20 (i - 14514) (by omega)
  rwa [show 14514 + (i - 14514) = i by omega] at hk

theorem stepUpTo_21 : ∀ i, 11954 ≤ i → i < 14770 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14642
  · exact stepUpTo_20 i hlo h
  have hk := sBlock21 (i - 14642) (by omega)
  rwa [show 14642 + (i - 14642) = i by omega] at hk

theorem stepUpTo_22 : ∀ i, 11954 ≤ i → i < 14898 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14770
  · exact stepUpTo_21 i hlo h
  have hk := sBlock22 (i - 14770) (by omega)
  rwa [show 14770 + (i - 14770) = i by omega] at hk

theorem stepUpTo_23 : ∀ i, 11954 ≤ i → i < 15026 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 14898
  · exact stepUpTo_22 i hlo h
  have hk := sBlock23 (i - 14898) (by omega)
  rwa [show 14898 + (i - 14898) = i by omega] at hk

theorem stepUpTo_24 : ∀ i, 11954 ≤ i → i < 15154 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15026
  · exact stepUpTo_23 i hlo h
  have hk := sBlock24 (i - 15026) (by omega)
  rwa [show 15026 + (i - 15026) = i by omega] at hk

theorem stepUpTo_25 : ∀ i, 11954 ≤ i → i < 15282 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15154
  · exact stepUpTo_24 i hlo h
  have hk := sBlock25 (i - 15154) (by omega)
  rwa [show 15154 + (i - 15154) = i by omega] at hk

theorem stepUpTo_26 : ∀ i, 11954 ≤ i → i < 15410 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15282
  · exact stepUpTo_25 i hlo h
  have hk := sBlock26 (i - 15282) (by omega)
  rwa [show 15282 + (i - 15282) = i by omega] at hk

theorem stepUpTo_27 : ∀ i, 11954 ≤ i → i < 15538 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15410
  · exact stepUpTo_26 i hlo h
  have hk := sBlock27 (i - 15410) (by omega)
  rwa [show 15410 + (i - 15410) = i by omega] at hk

theorem stepUpTo_28 : ∀ i, 11954 ≤ i → i < 15666 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15538
  · exact stepUpTo_27 i hlo h
  have hk := sBlock28 (i - 15538) (by omega)
  rwa [show 15538 + (i - 15538) = i by omega] at hk

theorem stepUpTo_29 : ∀ i, 11954 ≤ i → i < 15794 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15666
  · exact stepUpTo_28 i hlo h
  have hk := sBlock29 (i - 15666) (by omega)
  rwa [show 15666 + (i - 15666) = i by omega] at hk

theorem stepUpTo_30 : ∀ i, 11954 ≤ i → i < 15922 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15794
  · exact stepUpTo_29 i hlo h
  have hk := sBlock30 (i - 15794) (by omega)
  rwa [show 15794 + (i - 15794) = i by omega] at hk

theorem stepUpTo_31 : ∀ i, 11954 ≤ i → i < 16050 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 15922
  · exact stepUpTo_30 i hlo h
  have hk := sBlock31 (i - 15922) (by omega)
  rwa [show 15922 + (i - 15922) = i by omega] at hk

theorem stepUpTo_32 : ∀ i, 11954 ≤ i → i < 16178 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16050
  · exact stepUpTo_31 i hlo h
  have hk := sBlock32 (i - 16050) (by omega)
  rwa [show 16050 + (i - 16050) = i by omega] at hk

theorem stepUpTo_33 : ∀ i, 11954 ≤ i → i < 16306 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16178
  · exact stepUpTo_32 i hlo h
  have hk := sBlock33 (i - 16178) (by omega)
  rwa [show 16178 + (i - 16178) = i by omega] at hk

theorem stepUpTo_34 : ∀ i, 11954 ≤ i → i < 16434 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16306
  · exact stepUpTo_33 i hlo h
  have hk := sBlock34 (i - 16306) (by omega)
  rwa [show 16306 + (i - 16306) = i by omega] at hk

theorem stepUpTo_35 : ∀ i, 11954 ≤ i → i < 16562 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16434
  · exact stepUpTo_34 i hlo h
  have hk := sBlock35 (i - 16434) (by omega)
  rwa [show 16434 + (i - 16434) = i by omega] at hk

theorem stepUpTo_36 : ∀ i, 11954 ≤ i → i < 16690 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16562
  · exact stepUpTo_35 i hlo h
  have hk := sBlock36 (i - 16562) (by omega)
  rwa [show 16562 + (i - 16562) = i by omega] at hk

theorem stepUpTo_37 : ∀ i, 11954 ≤ i → i < 16818 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16690
  · exact stepUpTo_36 i hlo h
  have hk := sBlock37 (i - 16690) (by omega)
  rwa [show 16690 + (i - 16690) = i by omega] at hk

theorem stepUpTo_38 : ∀ i, 11954 ≤ i → i < 16946 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16818
  · exact stepUpTo_37 i hlo h
  have hk := sBlock38 (i - 16818) (by omega)
  rwa [show 16818 + (i - 16818) = i by omega] at hk

theorem stepUpTo_39 : ∀ i, 11954 ≤ i → i < 17074 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 16946
  · exact stepUpTo_38 i hlo h
  have hk := sBlock39 (i - 16946) (by omega)
  rwa [show 16946 + (i - 16946) = i by omega] at hk

theorem stepUpTo_40 : ∀ i, 11954 ≤ i → i < 17202 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17074
  · exact stepUpTo_39 i hlo h
  have hk := sBlock40 (i - 17074) (by omega)
  rwa [show 17074 + (i - 17074) = i by omega] at hk

theorem stepUpTo_41 : ∀ i, 11954 ≤ i → i < 17330 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17202
  · exact stepUpTo_40 i hlo h
  have hk := sBlock41 (i - 17202) (by omega)
  rwa [show 17202 + (i - 17202) = i by omega] at hk

theorem stepUpTo_42 : ∀ i, 11954 ≤ i → i < 17458 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17330
  · exact stepUpTo_41 i hlo h
  have hk := sBlock42 (i - 17330) (by omega)
  rwa [show 17330 + (i - 17330) = i by omega] at hk

theorem stepUpTo_43 : ∀ i, 11954 ≤ i → i < 17586 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17458
  · exact stepUpTo_42 i hlo h
  have hk := sBlock43 (i - 17458) (by omega)
  rwa [show 17458 + (i - 17458) = i by omega] at hk

theorem stepUpTo_44 : ∀ i, 11954 ≤ i → i < 17714 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17586
  · exact stepUpTo_43 i hlo h
  have hk := sBlock44 (i - 17586) (by omega)
  rwa [show 17586 + (i - 17586) = i by omega] at hk

theorem stepUpTo_45 : ∀ i, 11954 ≤ i → i < 17842 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17714
  · exact stepUpTo_44 i hlo h
  have hk := sBlock45 (i - 17714) (by omega)
  rwa [show 17714 + (i - 17714) = i by omega] at hk

theorem stepUpTo_46 : ∀ i, 11954 ≤ i → i < 17970 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17842
  · exact stepUpTo_45 i hlo h
  have hk := sBlock46 (i - 17842) (by omega)
  rwa [show 17842 + (i - 17842) = i by omega] at hk

theorem stepUpTo_47 : ∀ i, 11954 ≤ i → i < 18098 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 17970
  · exact stepUpTo_46 i hlo h
  have hk := sBlock47 (i - 17970) (by omega)
  rwa [show 17970 + (i - 17970) = i by omega] at hk

theorem stepUpTo_48 : ∀ i, 11954 ≤ i → i < 18226 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18098
  · exact stepUpTo_47 i hlo h
  have hk := sBlock48 (i - 18098) (by omega)
  rwa [show 18098 + (i - 18098) = i by omega] at hk

theorem stepUpTo_49 : ∀ i, 11954 ≤ i → i < 18354 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18226
  · exact stepUpTo_48 i hlo h
  have hk := sBlock49 (i - 18226) (by omega)
  rwa [show 18226 + (i - 18226) = i by omega] at hk

theorem stepUpTo_50 : ∀ i, 11954 ≤ i → i < 18482 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18354
  · exact stepUpTo_49 i hlo h
  have hk := sBlock50 (i - 18354) (by omega)
  rwa [show 18354 + (i - 18354) = i by omega] at hk

theorem stepUpTo_51 : ∀ i, 11954 ≤ i → i < 18610 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18482
  · exact stepUpTo_50 i hlo h
  have hk := sBlock51 (i - 18482) (by omega)
  rwa [show 18482 + (i - 18482) = i by omega] at hk

theorem stepUpTo_52 : ∀ i, 11954 ≤ i → i < 18738 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18610
  · exact stepUpTo_51 i hlo h
  have hk := sBlock52 (i - 18610) (by omega)
  rwa [show 18610 + (i - 18610) = i by omega] at hk

theorem stepUpTo_53 : ∀ i, 11954 ≤ i → i < 18866 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18738
  · exact stepUpTo_52 i hlo h
  have hk := sBlock53 (i - 18738) (by omega)
  rwa [show 18738 + (i - 18738) = i by omega] at hk

theorem stepUpTo_54 : ∀ i, 11954 ≤ i → i < 18994 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18866
  · exact stepUpTo_53 i hlo h
  have hk := sBlock54 (i - 18866) (by omega)
  rwa [show 18866 + (i - 18866) = i by omega] at hk

theorem stepUpTo_55 : ∀ i, 11954 ≤ i → i < 19122 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 18994
  · exact stepUpTo_54 i hlo h
  have hk := sBlock55 (i - 18994) (by omega)
  rwa [show 18994 + (i - 18994) = i by omega] at hk

theorem stepUpTo_56 : ∀ i, 11954 ≤ i → i < 19250 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19122
  · exact stepUpTo_55 i hlo h
  have hk := sBlock56 (i - 19122) (by omega)
  rwa [show 19122 + (i - 19122) = i by omega] at hk

theorem stepUpTo_57 : ∀ i, 11954 ≤ i → i < 19378 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19250
  · exact stepUpTo_56 i hlo h
  have hk := sBlock57 (i - 19250) (by omega)
  rwa [show 19250 + (i - 19250) = i by omega] at hk

theorem stepUpTo_58 : ∀ i, 11954 ≤ i → i < 19506 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19378
  · exact stepUpTo_57 i hlo h
  have hk := sBlock58 (i - 19378) (by omega)
  rwa [show 19378 + (i - 19378) = i by omega] at hk

theorem stepUpTo_59 : ∀ i, 11954 ≤ i → i < 19634 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19506
  · exact stepUpTo_58 i hlo h
  have hk := sBlock59 (i - 19506) (by omega)
  rwa [show 19506 + (i - 19506) = i by omega] at hk

theorem stepUpTo_60 : ∀ i, 11954 ≤ i → i < 19762 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19634
  · exact stepUpTo_59 i hlo h
  have hk := sBlock60 (i - 19634) (by omega)
  rwa [show 19634 + (i - 19634) = i by omega] at hk

theorem stepUpTo_61 : ∀ i, 11954 ≤ i → i < 19890 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19762
  · exact stepUpTo_60 i hlo h
  have hk := sBlock61 (i - 19762) (by omega)
  rwa [show 19762 + (i - 19762) = i by omega] at hk

theorem stepUpTo_62 : ∀ i, 11954 ≤ i → i < 20018 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 19890
  · exact stepUpTo_61 i hlo h
  have hk := sBlock62 (i - 19890) (by omega)
  rwa [show 19890 + (i - 19890) = i by omega] at hk

theorem stepUpTo_63 : ∀ i, 11954 ≤ i → i < 20146 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20018
  · exact stepUpTo_62 i hlo h
  have hk := sBlock63 (i - 20018) (by omega)
  rwa [show 20018 + (i - 20018) = i by omega] at hk

theorem stepUpTo_64 : ∀ i, 11954 ≤ i → i < 20274 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20146
  · exact stepUpTo_63 i hlo h
  have hk := sBlock64 (i - 20146) (by omega)
  rwa [show 20146 + (i - 20146) = i by omega] at hk

theorem stepUpTo_65 : ∀ i, 11954 ≤ i → i < 20402 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20274
  · exact stepUpTo_64 i hlo h
  have hk := sBlock65 (i - 20274) (by omega)
  rwa [show 20274 + (i - 20274) = i by omega] at hk

theorem stepUpTo_66 : ∀ i, 11954 ≤ i → i < 20530 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20402
  · exact stepUpTo_65 i hlo h
  have hk := sBlock66 (i - 20402) (by omega)
  rwa [show 20402 + (i - 20402) = i by omega] at hk

theorem stepUpTo_67 : ∀ i, 11954 ≤ i → i < 20658 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20530
  · exact stepUpTo_66 i hlo h
  have hk := sBlock67 (i - 20530) (by omega)
  rwa [show 20530 + (i - 20530) = i by omega] at hk

theorem stepUpTo_68 : ∀ i, 11954 ≤ i → i < 20786 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20658
  · exact stepUpTo_67 i hlo h
  have hk := sBlock68 (i - 20658) (by omega)
  rwa [show 20658 + (i - 20658) = i by omega] at hk

theorem stepUpTo_69 : ∀ i, 11954 ≤ i → i < 20914 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20786
  · exact stepUpTo_68 i hlo h
  have hk := sBlock69 (i - 20786) (by omega)
  rwa [show 20786 + (i - 20786) = i by omega] at hk

theorem stepUpTo_70 : ∀ i, 11954 ≤ i → i < 21042 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 20914
  · exact stepUpTo_69 i hlo h
  have hk := sBlock70 (i - 20914) (by omega)
  rwa [show 20914 + (i - 20914) = i by omega] at hk

theorem stepUpTo_71 : ∀ i, 11954 ≤ i → i < 21170 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21042
  · exact stepUpTo_70 i hlo h
  have hk := sBlock71 (i - 21042) (by omega)
  rwa [show 21042 + (i - 21042) = i by omega] at hk

theorem stepUpTo_72 : ∀ i, 11954 ≤ i → i < 21298 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21170
  · exact stepUpTo_71 i hlo h
  have hk := sBlock72 (i - 21170) (by omega)
  rwa [show 21170 + (i - 21170) = i by omega] at hk

theorem stepUpTo_73 : ∀ i, 11954 ≤ i → i < 21426 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21298
  · exact stepUpTo_72 i hlo h
  have hk := sBlock73 (i - 21298) (by omega)
  rwa [show 21298 + (i - 21298) = i by omega] at hk

theorem stepUpTo_74 : ∀ i, 11954 ≤ i → i < 21554 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21426
  · exact stepUpTo_73 i hlo h
  have hk := sBlock74 (i - 21426) (by omega)
  rwa [show 21426 + (i - 21426) = i by omega] at hk

theorem stepUpTo_75 : ∀ i, 11954 ≤ i → i < 21682 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21554
  · exact stepUpTo_74 i hlo h
  have hk := sBlock75 (i - 21554) (by omega)
  rwa [show 21554 + (i - 21554) = i by omega] at hk

theorem stepUpTo_76 : ∀ i, 11954 ≤ i → i < 21810 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21682
  · exact stepUpTo_75 i hlo h
  have hk := sBlock76 (i - 21682) (by omega)
  rwa [show 21682 + (i - 21682) = i by omega] at hk

theorem stepUpTo_77 : ∀ i, 11954 ≤ i → i < 21938 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21810
  · exact stepUpTo_76 i hlo h
  have hk := sBlock77 (i - 21810) (by omega)
  rwa [show 21810 + (i - 21810) = i by omega] at hk

theorem stepUpTo_78 : ∀ i, 11954 ≤ i → i < 22066 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 21938
  · exact stepUpTo_77 i hlo h
  have hk := sBlock78 (i - 21938) (by omega)
  rwa [show 21938 + (i - 21938) = i by omega] at hk

theorem stepUpTo_79 : ∀ i, 11954 ≤ i → i < 22194 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22066
  · exact stepUpTo_78 i hlo h
  have hk := sBlock79 (i - 22066) (by omega)
  rwa [show 22066 + (i - 22066) = i by omega] at hk

theorem stepUpTo_80 : ∀ i, 11954 ≤ i → i < 22322 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22194
  · exact stepUpTo_79 i hlo h
  have hk := sBlock80 (i - 22194) (by omega)
  rwa [show 22194 + (i - 22194) = i by omega] at hk

theorem stepUpTo_81 : ∀ i, 11954 ≤ i → i < 22354 → BitRUP.StepValid rupClauses rupHints i := by
  intro i hlo hi
  by_cases h : i < 22322
  · exact stepUpTo_80 i hlo h
  have hk := sBlock81 (i - 22322) (by omega)
  rwa [show 22322 + (i - 22322) = i by omega] at hk

/-- Check S3_21_137_t36: the target is covered by the check's list, or is a ray centre. -/
theorem check (z : ℤ) (hz : E.target.Matches primes z) :
    (∃ i < 618413, (E.fam i).Matches primes z) ∨ ∃ j, ∃ r ∈ (lds j).rays, z = r.center :=
  E.cover_bit lds_valid masks_ok tgt_ok rupClauses rupHints origin 11954 22354 22353
    initUpTo_93 stepUpTo_81 (by decide) final_ok z hz

end UC85.W.C.S3_21_137_t36
