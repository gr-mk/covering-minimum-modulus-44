import UC85.W.U.MBLOCK0
import UC85.W.U.MBLOCK1
import UC85.W.U.MBLOCK2
import UC85.W.U.MBLOCK3
import UC85.W.U.MBLOCK4
import UC85.W.U.MBLOCK5
import UC85.W.U.MBLOCK6
import UC85.W.U.MBLOCK7
import UC85.W.U.MBLOCK8
import UC85.W.U.MBLOCK9
import UC85.W.U.MBLOCK10
import UC85.W.U.MBLOCK11
import UC85.W.U.MBLOCK12
import UC85.W.U.MBLOCK13
import UC85.W.U.MBLOCK14
import UC85.W.U.MBLOCK15
import UC85.W.U.MBLOCK16
import UC85.W.U.MBLOCK17
import UC85.W.U.MBLOCK18
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.U
open Modulus40

theorem minUpTo_0 : ∀ i, i < 512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  have hk := mBlock0 (i - 0) (by omega)
  rwa [show 0 + (i - 0) = i by omega] at hk

theorem minUpTo_1 : ∀ i, i < 1024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 512
  · exact minUpTo_0 i h
  have hk := mBlock1 (i - 512) (by omega)
  rwa [show 512 + (i - 512) = i by omega] at hk

theorem minUpTo_2 : ∀ i, i < 1536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 1024
  · exact minUpTo_1 i h
  have hk := mBlock2 (i - 1024) (by omega)
  rwa [show 1024 + (i - 1024) = i by omega] at hk

theorem minUpTo_3 : ∀ i, i < 2048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 1536
  · exact minUpTo_2 i h
  have hk := mBlock3 (i - 1536) (by omega)
  rwa [show 1536 + (i - 1536) = i by omega] at hk

theorem minUpTo_4 : ∀ i, i < 2560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 2048
  · exact minUpTo_3 i h
  have hk := mBlock4 (i - 2048) (by omega)
  rwa [show 2048 + (i - 2048) = i by omega] at hk

theorem minUpTo_5 : ∀ i, i < 3072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 2560
  · exact minUpTo_4 i h
  have hk := mBlock5 (i - 2560) (by omega)
  rwa [show 2560 + (i - 2560) = i by omega] at hk

theorem minUpTo_6 : ∀ i, i < 3584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 3072
  · exact minUpTo_5 i h
  have hk := mBlock6 (i - 3072) (by omega)
  rwa [show 3072 + (i - 3072) = i by omega] at hk

theorem minUpTo_7 : ∀ i, i < 4096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 3584
  · exact minUpTo_6 i h
  have hk := mBlock7 (i - 3584) (by omega)
  rwa [show 3584 + (i - 3584) = i by omega] at hk

theorem minUpTo_8 : ∀ i, i < 4608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 4096
  · exact minUpTo_7 i h
  have hk := mBlock8 (i - 4096) (by omega)
  rwa [show 4096 + (i - 4096) = i by omega] at hk

theorem minUpTo_9 : ∀ i, i < 5120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 4608
  · exact minUpTo_8 i h
  have hk := mBlock9 (i - 4608) (by omega)
  rwa [show 4608 + (i - 4608) = i by omega] at hk

theorem minUpTo_10 : ∀ i, i < 5632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 5120
  · exact minUpTo_9 i h
  have hk := mBlock10 (i - 5120) (by omega)
  rwa [show 5120 + (i - 5120) = i by omega] at hk

theorem minUpTo_11 : ∀ i, i < 6144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 5632
  · exact minUpTo_10 i h
  have hk := mBlock11 (i - 5632) (by omega)
  rwa [show 5632 + (i - 5632) = i by omega] at hk

theorem minUpTo_12 : ∀ i, i < 6656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 6144
  · exact minUpTo_11 i h
  have hk := mBlock12 (i - 6144) (by omega)
  rwa [show 6144 + (i - 6144) = i by omega] at hk

theorem minUpTo_13 : ∀ i, i < 7168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 6656
  · exact minUpTo_12 i h
  have hk := mBlock13 (i - 6656) (by omega)
  rwa [show 6656 + (i - 6656) = i by omega] at hk

theorem minUpTo_14 : ∀ i, i < 7680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 7168
  · exact minUpTo_13 i h
  have hk := mBlock14 (i - 7168) (by omega)
  rwa [show 7168 + (i - 7168) = i by omega] at hk

theorem minUpTo_15 : ∀ i, i < 8192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 7680
  · exact minUpTo_14 i h
  have hk := mBlock15 (i - 7680) (by omega)
  rwa [show 7680 + (i - 7680) = i by omega] at hk

theorem minUpTo_16 : ∀ i, i < 8704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 8192
  · exact minUpTo_15 i h
  have hk := mBlock16 (i - 8192) (by omega)
  rwa [show 8192 + (i - 8192) = i by omega] at hk

theorem minUpTo_17 : ∀ i, i < 9216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 8704
  · exact minUpTo_16 i h
  have hk := mBlock17 (i - 8704) (by omega)
  rwa [show 8704 + (i - 8704) = i by omega] at hk

theorem minUpTo_18 : ∀ i, i < 9728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 9216
  · exact minUpTo_17 i h
  have hk := mBlock18 (i - 9216) (by omega)
  rwa [show 9216 + (i - 9216) = i by omega] at hk

theorem minUpTo_19 : ∀ i, i < 10240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 9728
  · exact minUpTo_18 i h
  have hk := mBlock19 (i - 9728) (by omega)
  rwa [show 9728 + (i - 9728) = i by omega] at hk

theorem minUpTo_20 : ∀ i, i < 10752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 10240
  · exact minUpTo_19 i h
  have hk := mBlock20 (i - 10240) (by omega)
  rwa [show 10240 + (i - 10240) = i by omega] at hk

theorem minUpTo_21 : ∀ i, i < 11264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 10752
  · exact minUpTo_20 i h
  have hk := mBlock21 (i - 10752) (by omega)
  rwa [show 10752 + (i - 10752) = i by omega] at hk

theorem minUpTo_22 : ∀ i, i < 11776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 11264
  · exact minUpTo_21 i h
  have hk := mBlock22 (i - 11264) (by omega)
  rwa [show 11264 + (i - 11264) = i by omega] at hk

theorem minUpTo_23 : ∀ i, i < 12288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 11776
  · exact minUpTo_22 i h
  have hk := mBlock23 (i - 11776) (by omega)
  rwa [show 11776 + (i - 11776) = i by omega] at hk

theorem minUpTo_24 : ∀ i, i < 12800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 12288
  · exact minUpTo_23 i h
  have hk := mBlock24 (i - 12288) (by omega)
  rwa [show 12288 + (i - 12288) = i by omega] at hk

theorem minUpTo_25 : ∀ i, i < 13312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 12800
  · exact minUpTo_24 i h
  have hk := mBlock25 (i - 12800) (by omega)
  rwa [show 12800 + (i - 12800) = i by omega] at hk

theorem minUpTo_26 : ∀ i, i < 13824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 13312
  · exact minUpTo_25 i h
  have hk := mBlock26 (i - 13312) (by omega)
  rwa [show 13312 + (i - 13312) = i by omega] at hk

theorem minUpTo_27 : ∀ i, i < 14336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 13824
  · exact minUpTo_26 i h
  have hk := mBlock27 (i - 13824) (by omega)
  rwa [show 13824 + (i - 13824) = i by omega] at hk

theorem minUpTo_28 : ∀ i, i < 14848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 14336
  · exact minUpTo_27 i h
  have hk := mBlock28 (i - 14336) (by omega)
  rwa [show 14336 + (i - 14336) = i by omega] at hk

theorem minUpTo_29 : ∀ i, i < 15360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 14848
  · exact minUpTo_28 i h
  have hk := mBlock29 (i - 14848) (by omega)
  rwa [show 14848 + (i - 14848) = i by omega] at hk

theorem minUpTo_30 : ∀ i, i < 15872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 15360
  · exact minUpTo_29 i h
  have hk := mBlock30 (i - 15360) (by omega)
  rwa [show 15360 + (i - 15360) = i by omega] at hk

theorem minUpTo_31 : ∀ i, i < 16384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 15872
  · exact minUpTo_30 i h
  have hk := mBlock31 (i - 15872) (by omega)
  rwa [show 15872 + (i - 15872) = i by omega] at hk

theorem minUpTo_32 : ∀ i, i < 16896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 16384
  · exact minUpTo_31 i h
  have hk := mBlock32 (i - 16384) (by omega)
  rwa [show 16384 + (i - 16384) = i by omega] at hk

theorem minUpTo_33 : ∀ i, i < 17408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 16896
  · exact minUpTo_32 i h
  have hk := mBlock33 (i - 16896) (by omega)
  rwa [show 16896 + (i - 16896) = i by omega] at hk

theorem minUpTo_34 : ∀ i, i < 17920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 17408
  · exact minUpTo_33 i h
  have hk := mBlock34 (i - 17408) (by omega)
  rwa [show 17408 + (i - 17408) = i by omega] at hk

theorem minUpTo_35 : ∀ i, i < 18432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 17920
  · exact minUpTo_34 i h
  have hk := mBlock35 (i - 17920) (by omega)
  rwa [show 17920 + (i - 17920) = i by omega] at hk

theorem minUpTo_36 : ∀ i, i < 18944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 18432
  · exact minUpTo_35 i h
  have hk := mBlock36 (i - 18432) (by omega)
  rwa [show 18432 + (i - 18432) = i by omega] at hk

theorem minUpTo_37 : ∀ i, i < 19456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 18944
  · exact minUpTo_36 i h
  have hk := mBlock37 (i - 18944) (by omega)
  rwa [show 18944 + (i - 18944) = i by omega] at hk

theorem minUpTo_38 : ∀ i, i < 19968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 19456
  · exact minUpTo_37 i h
  have hk := mBlock38 (i - 19456) (by omega)
  rwa [show 19456 + (i - 19456) = i by omega] at hk

theorem minUpTo_39 : ∀ i, i < 20480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 19968
  · exact minUpTo_38 i h
  have hk := mBlock39 (i - 19968) (by omega)
  rwa [show 19968 + (i - 19968) = i by omega] at hk

theorem minUpTo_40 : ∀ i, i < 20992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 20480
  · exact minUpTo_39 i h
  have hk := mBlock40 (i - 20480) (by omega)
  rwa [show 20480 + (i - 20480) = i by omega] at hk

theorem minUpTo_41 : ∀ i, i < 21504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 20992
  · exact minUpTo_40 i h
  have hk := mBlock41 (i - 20992) (by omega)
  rwa [show 20992 + (i - 20992) = i by omega] at hk

theorem minUpTo_42 : ∀ i, i < 22016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 21504
  · exact minUpTo_41 i h
  have hk := mBlock42 (i - 21504) (by omega)
  rwa [show 21504 + (i - 21504) = i by omega] at hk

theorem minUpTo_43 : ∀ i, i < 22528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 22016
  · exact minUpTo_42 i h
  have hk := mBlock43 (i - 22016) (by omega)
  rwa [show 22016 + (i - 22016) = i by omega] at hk

theorem minUpTo_44 : ∀ i, i < 23040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 22528
  · exact minUpTo_43 i h
  have hk := mBlock44 (i - 22528) (by omega)
  rwa [show 22528 + (i - 22528) = i by omega] at hk

theorem minUpTo_45 : ∀ i, i < 23552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 23040
  · exact minUpTo_44 i h
  have hk := mBlock45 (i - 23040) (by omega)
  rwa [show 23040 + (i - 23040) = i by omega] at hk

theorem minUpTo_46 : ∀ i, i < 24064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 23552
  · exact minUpTo_45 i h
  have hk := mBlock46 (i - 23552) (by omega)
  rwa [show 23552 + (i - 23552) = i by omega] at hk

theorem minUpTo_47 : ∀ i, i < 24576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 24064
  · exact minUpTo_46 i h
  have hk := mBlock47 (i - 24064) (by omega)
  rwa [show 24064 + (i - 24064) = i by omega] at hk

theorem minUpTo_48 : ∀ i, i < 25088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 24576
  · exact minUpTo_47 i h
  have hk := mBlock48 (i - 24576) (by omega)
  rwa [show 24576 + (i - 24576) = i by omega] at hk

theorem minUpTo_49 : ∀ i, i < 25600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 25088
  · exact minUpTo_48 i h
  have hk := mBlock49 (i - 25088) (by omega)
  rwa [show 25088 + (i - 25088) = i by omega] at hk

theorem minUpTo_50 : ∀ i, i < 26112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 25600
  · exact minUpTo_49 i h
  have hk := mBlock50 (i - 25600) (by omega)
  rwa [show 25600 + (i - 25600) = i by omega] at hk

theorem minUpTo_51 : ∀ i, i < 26624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 26112
  · exact minUpTo_50 i h
  have hk := mBlock51 (i - 26112) (by omega)
  rwa [show 26112 + (i - 26112) = i by omega] at hk

theorem minUpTo_52 : ∀ i, i < 27136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 26624
  · exact minUpTo_51 i h
  have hk := mBlock52 (i - 26624) (by omega)
  rwa [show 26624 + (i - 26624) = i by omega] at hk

theorem minUpTo_53 : ∀ i, i < 27648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 27136
  · exact minUpTo_52 i h
  have hk := mBlock53 (i - 27136) (by omega)
  rwa [show 27136 + (i - 27136) = i by omega] at hk

theorem minUpTo_54 : ∀ i, i < 28160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 27648
  · exact minUpTo_53 i h
  have hk := mBlock54 (i - 27648) (by omega)
  rwa [show 27648 + (i - 27648) = i by omega] at hk

theorem minUpTo_55 : ∀ i, i < 28672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 28160
  · exact minUpTo_54 i h
  have hk := mBlock55 (i - 28160) (by omega)
  rwa [show 28160 + (i - 28160) = i by omega] at hk

theorem minUpTo_56 : ∀ i, i < 29184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 28672
  · exact minUpTo_55 i h
  have hk := mBlock56 (i - 28672) (by omega)
  rwa [show 28672 + (i - 28672) = i by omega] at hk

theorem minUpTo_57 : ∀ i, i < 29696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 29184
  · exact minUpTo_56 i h
  have hk := mBlock57 (i - 29184) (by omega)
  rwa [show 29184 + (i - 29184) = i by omega] at hk

theorem minUpTo_58 : ∀ i, i < 30208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 29696
  · exact minUpTo_57 i h
  have hk := mBlock58 (i - 29696) (by omega)
  rwa [show 29696 + (i - 29696) = i by omega] at hk

theorem minUpTo_59 : ∀ i, i < 30720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 30208
  · exact minUpTo_58 i h
  have hk := mBlock59 (i - 30208) (by omega)
  rwa [show 30208 + (i - 30208) = i by omega] at hk

theorem minUpTo_60 : ∀ i, i < 31232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 30720
  · exact minUpTo_59 i h
  have hk := mBlock60 (i - 30720) (by omega)
  rwa [show 30720 + (i - 30720) = i by omega] at hk

theorem minUpTo_61 : ∀ i, i < 31744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 31232
  · exact minUpTo_60 i h
  have hk := mBlock61 (i - 31232) (by omega)
  rwa [show 31232 + (i - 31232) = i by omega] at hk

theorem minUpTo_62 : ∀ i, i < 32256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 31744
  · exact minUpTo_61 i h
  have hk := mBlock62 (i - 31744) (by omega)
  rwa [show 31744 + (i - 31744) = i by omega] at hk

theorem minUpTo_63 : ∀ i, i < 32768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 32256
  · exact minUpTo_62 i h
  have hk := mBlock63 (i - 32256) (by omega)
  rwa [show 32256 + (i - 32256) = i by omega] at hk

theorem minUpTo_64 : ∀ i, i < 33280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 32768
  · exact minUpTo_63 i h
  have hk := mBlock64 (i - 32768) (by omega)
  rwa [show 32768 + (i - 32768) = i by omega] at hk

theorem minUpTo_65 : ∀ i, i < 33792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 33280
  · exact minUpTo_64 i h
  have hk := mBlock65 (i - 33280) (by omega)
  rwa [show 33280 + (i - 33280) = i by omega] at hk

theorem minUpTo_66 : ∀ i, i < 34304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 33792
  · exact minUpTo_65 i h
  have hk := mBlock66 (i - 33792) (by omega)
  rwa [show 33792 + (i - 33792) = i by omega] at hk

theorem minUpTo_67 : ∀ i, i < 34816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 34304
  · exact minUpTo_66 i h
  have hk := mBlock67 (i - 34304) (by omega)
  rwa [show 34304 + (i - 34304) = i by omega] at hk

theorem minUpTo_68 : ∀ i, i < 35328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 34816
  · exact minUpTo_67 i h
  have hk := mBlock68 (i - 34816) (by omega)
  rwa [show 34816 + (i - 34816) = i by omega] at hk

theorem minUpTo_69 : ∀ i, i < 35840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 35328
  · exact minUpTo_68 i h
  have hk := mBlock69 (i - 35328) (by omega)
  rwa [show 35328 + (i - 35328) = i by omega] at hk

theorem minUpTo_70 : ∀ i, i < 36352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 35840
  · exact minUpTo_69 i h
  have hk := mBlock70 (i - 35840) (by omega)
  rwa [show 35840 + (i - 35840) = i by omega] at hk

theorem minUpTo_71 : ∀ i, i < 36864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 36352
  · exact minUpTo_70 i h
  have hk := mBlock71 (i - 36352) (by omega)
  rwa [show 36352 + (i - 36352) = i by omega] at hk

theorem minUpTo_72 : ∀ i, i < 37376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 36864
  · exact minUpTo_71 i h
  have hk := mBlock72 (i - 36864) (by omega)
  rwa [show 36864 + (i - 36864) = i by omega] at hk

theorem minUpTo_73 : ∀ i, i < 37888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 37376
  · exact minUpTo_72 i h
  have hk := mBlock73 (i - 37376) (by omega)
  rwa [show 37376 + (i - 37376) = i by omega] at hk

theorem minUpTo_74 : ∀ i, i < 38400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 37888
  · exact minUpTo_73 i h
  have hk := mBlock74 (i - 37888) (by omega)
  rwa [show 37888 + (i - 37888) = i by omega] at hk

theorem minUpTo_75 : ∀ i, i < 38912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 38400
  · exact minUpTo_74 i h
  have hk := mBlock75 (i - 38400) (by omega)
  rwa [show 38400 + (i - 38400) = i by omega] at hk

theorem minUpTo_76 : ∀ i, i < 39424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 38912
  · exact minUpTo_75 i h
  have hk := mBlock76 (i - 38912) (by omega)
  rwa [show 38912 + (i - 38912) = i by omega] at hk

theorem minUpTo_77 : ∀ i, i < 39936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 39424
  · exact minUpTo_76 i h
  have hk := mBlock77 (i - 39424) (by omega)
  rwa [show 39424 + (i - 39424) = i by omega] at hk

theorem minUpTo_78 : ∀ i, i < 40448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 39936
  · exact minUpTo_77 i h
  have hk := mBlock78 (i - 39936) (by omega)
  rwa [show 39936 + (i - 39936) = i by omega] at hk

theorem minUpTo_79 : ∀ i, i < 40960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 40448
  · exact minUpTo_78 i h
  have hk := mBlock79 (i - 40448) (by omega)
  rwa [show 40448 + (i - 40448) = i by omega] at hk

theorem minUpTo_80 : ∀ i, i < 41472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 40960
  · exact minUpTo_79 i h
  have hk := mBlock80 (i - 40960) (by omega)
  rwa [show 40960 + (i - 40960) = i by omega] at hk

theorem minUpTo_81 : ∀ i, i < 41984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 41472
  · exact minUpTo_80 i h
  have hk := mBlock81 (i - 41472) (by omega)
  rwa [show 41472 + (i - 41472) = i by omega] at hk

theorem minUpTo_82 : ∀ i, i < 42496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 41984
  · exact minUpTo_81 i h
  have hk := mBlock82 (i - 41984) (by omega)
  rwa [show 41984 + (i - 41984) = i by omega] at hk

theorem minUpTo_83 : ∀ i, i < 43008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 42496
  · exact minUpTo_82 i h
  have hk := mBlock83 (i - 42496) (by omega)
  rwa [show 42496 + (i - 42496) = i by omega] at hk

theorem minUpTo_84 : ∀ i, i < 43520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 43008
  · exact minUpTo_83 i h
  have hk := mBlock84 (i - 43008) (by omega)
  rwa [show 43008 + (i - 43008) = i by omega] at hk

theorem minUpTo_85 : ∀ i, i < 44032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 43520
  · exact minUpTo_84 i h
  have hk := mBlock85 (i - 43520) (by omega)
  rwa [show 43520 + (i - 43520) = i by omega] at hk

theorem minUpTo_86 : ∀ i, i < 44544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 44032
  · exact minUpTo_85 i h
  have hk := mBlock86 (i - 44032) (by omega)
  rwa [show 44032 + (i - 44032) = i by omega] at hk

theorem minUpTo_87 : ∀ i, i < 45056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 44544
  · exact minUpTo_86 i h
  have hk := mBlock87 (i - 44544) (by omega)
  rwa [show 44544 + (i - 44544) = i by omega] at hk

theorem minUpTo_88 : ∀ i, i < 45568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 45056
  · exact minUpTo_87 i h
  have hk := mBlock88 (i - 45056) (by omega)
  rwa [show 45056 + (i - 45056) = i by omega] at hk

theorem minUpTo_89 : ∀ i, i < 46080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 45568
  · exact minUpTo_88 i h
  have hk := mBlock89 (i - 45568) (by omega)
  rwa [show 45568 + (i - 45568) = i by omega] at hk

theorem minUpTo_90 : ∀ i, i < 46592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 46080
  · exact minUpTo_89 i h
  have hk := mBlock90 (i - 46080) (by omega)
  rwa [show 46080 + (i - 46080) = i by omega] at hk

theorem minUpTo_91 : ∀ i, i < 47104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 46592
  · exact minUpTo_90 i h
  have hk := mBlock91 (i - 46592) (by omega)
  rwa [show 46592 + (i - 46592) = i by omega] at hk

theorem minUpTo_92 : ∀ i, i < 47616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 47104
  · exact minUpTo_91 i h
  have hk := mBlock92 (i - 47104) (by omega)
  rwa [show 47104 + (i - 47104) = i by omega] at hk

theorem minUpTo_93 : ∀ i, i < 48128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 47616
  · exact minUpTo_92 i h
  have hk := mBlock93 (i - 47616) (by omega)
  rwa [show 47616 + (i - 47616) = i by omega] at hk

theorem minUpTo_94 : ∀ i, i < 48640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 48128
  · exact minUpTo_93 i h
  have hk := mBlock94 (i - 48128) (by omega)
  rwa [show 48128 + (i - 48128) = i by omega] at hk

theorem minUpTo_95 : ∀ i, i < 49152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 48640
  · exact minUpTo_94 i h
  have hk := mBlock95 (i - 48640) (by omega)
  rwa [show 48640 + (i - 48640) = i by omega] at hk

theorem minUpTo_96 : ∀ i, i < 49664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 49152
  · exact minUpTo_95 i h
  have hk := mBlock96 (i - 49152) (by omega)
  rwa [show 49152 + (i - 49152) = i by omega] at hk

theorem minUpTo_97 : ∀ i, i < 50176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 49664
  · exact minUpTo_96 i h
  have hk := mBlock97 (i - 49664) (by omega)
  rwa [show 49664 + (i - 49664) = i by omega] at hk

theorem minUpTo_98 : ∀ i, i < 50688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 50176
  · exact minUpTo_97 i h
  have hk := mBlock98 (i - 50176) (by omega)
  rwa [show 50176 + (i - 50176) = i by omega] at hk

theorem minUpTo_99 : ∀ i, i < 51200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 50688
  · exact minUpTo_98 i h
  have hk := mBlock99 (i - 50688) (by omega)
  rwa [show 50688 + (i - 50688) = i by omega] at hk

theorem minUpTo_100 : ∀ i, i < 51712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 51200
  · exact minUpTo_99 i h
  have hk := mBlock100 (i - 51200) (by omega)
  rwa [show 51200 + (i - 51200) = i by omega] at hk

theorem minUpTo_101 : ∀ i, i < 52224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 51712
  · exact minUpTo_100 i h
  have hk := mBlock101 (i - 51712) (by omega)
  rwa [show 51712 + (i - 51712) = i by omega] at hk

theorem minUpTo_102 : ∀ i, i < 52736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 52224
  · exact minUpTo_101 i h
  have hk := mBlock102 (i - 52224) (by omega)
  rwa [show 52224 + (i - 52224) = i by omega] at hk

theorem minUpTo_103 : ∀ i, i < 53248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 52736
  · exact minUpTo_102 i h
  have hk := mBlock103 (i - 52736) (by omega)
  rwa [show 52736 + (i - 52736) = i by omega] at hk

theorem minUpTo_104 : ∀ i, i < 53760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 53248
  · exact minUpTo_103 i h
  have hk := mBlock104 (i - 53248) (by omega)
  rwa [show 53248 + (i - 53248) = i by omega] at hk

theorem minUpTo_105 : ∀ i, i < 54272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 53760
  · exact minUpTo_104 i h
  have hk := mBlock105 (i - 53760) (by omega)
  rwa [show 53760 + (i - 53760) = i by omega] at hk

theorem minUpTo_106 : ∀ i, i < 54784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 54272
  · exact minUpTo_105 i h
  have hk := mBlock106 (i - 54272) (by omega)
  rwa [show 54272 + (i - 54272) = i by omega] at hk

theorem minUpTo_107 : ∀ i, i < 55296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 54784
  · exact minUpTo_106 i h
  have hk := mBlock107 (i - 54784) (by omega)
  rwa [show 54784 + (i - 54784) = i by omega] at hk

theorem minUpTo_108 : ∀ i, i < 55808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 55296
  · exact minUpTo_107 i h
  have hk := mBlock108 (i - 55296) (by omega)
  rwa [show 55296 + (i - 55296) = i by omega] at hk

theorem minUpTo_109 : ∀ i, i < 56320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 55808
  · exact minUpTo_108 i h
  have hk := mBlock109 (i - 55808) (by omega)
  rwa [show 55808 + (i - 55808) = i by omega] at hk

theorem minUpTo_110 : ∀ i, i < 56832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 56320
  · exact minUpTo_109 i h
  have hk := mBlock110 (i - 56320) (by omega)
  rwa [show 56320 + (i - 56320) = i by omega] at hk

theorem minUpTo_111 : ∀ i, i < 57344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 56832
  · exact minUpTo_110 i h
  have hk := mBlock111 (i - 56832) (by omega)
  rwa [show 56832 + (i - 56832) = i by omega] at hk

theorem minUpTo_112 : ∀ i, i < 57856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 57344
  · exact minUpTo_111 i h
  have hk := mBlock112 (i - 57344) (by omega)
  rwa [show 57344 + (i - 57344) = i by omega] at hk

theorem minUpTo_113 : ∀ i, i < 58368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 57856
  · exact minUpTo_112 i h
  have hk := mBlock113 (i - 57856) (by omega)
  rwa [show 57856 + (i - 57856) = i by omega] at hk

theorem minUpTo_114 : ∀ i, i < 58880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 58368
  · exact minUpTo_113 i h
  have hk := mBlock114 (i - 58368) (by omega)
  rwa [show 58368 + (i - 58368) = i by omega] at hk

theorem minUpTo_115 : ∀ i, i < 59392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 58880
  · exact minUpTo_114 i h
  have hk := mBlock115 (i - 58880) (by omega)
  rwa [show 58880 + (i - 58880) = i by omega] at hk

theorem minUpTo_116 : ∀ i, i < 59904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 59392
  · exact minUpTo_115 i h
  have hk := mBlock116 (i - 59392) (by omega)
  rwa [show 59392 + (i - 59392) = i by omega] at hk

theorem minUpTo_117 : ∀ i, i < 60416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 59904
  · exact minUpTo_116 i h
  have hk := mBlock117 (i - 59904) (by omega)
  rwa [show 59904 + (i - 59904) = i by omega] at hk

theorem minUpTo_118 : ∀ i, i < 60928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 60416
  · exact minUpTo_117 i h
  have hk := mBlock118 (i - 60416) (by omega)
  rwa [show 60416 + (i - 60416) = i by omega] at hk

theorem minUpTo_119 : ∀ i, i < 61440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 60928
  · exact minUpTo_118 i h
  have hk := mBlock119 (i - 60928) (by omega)
  rwa [show 60928 + (i - 60928) = i by omega] at hk

theorem minUpTo_120 : ∀ i, i < 61952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 61440
  · exact minUpTo_119 i h
  have hk := mBlock120 (i - 61440) (by omega)
  rwa [show 61440 + (i - 61440) = i by omega] at hk

theorem minUpTo_121 : ∀ i, i < 62464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 61952
  · exact minUpTo_120 i h
  have hk := mBlock121 (i - 61952) (by omega)
  rwa [show 61952 + (i - 61952) = i by omega] at hk

theorem minUpTo_122 : ∀ i, i < 62976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 62464
  · exact minUpTo_121 i h
  have hk := mBlock122 (i - 62464) (by omega)
  rwa [show 62464 + (i - 62464) = i by omega] at hk

theorem minUpTo_123 : ∀ i, i < 63488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 62976
  · exact minUpTo_122 i h
  have hk := mBlock123 (i - 62976) (by omega)
  rwa [show 62976 + (i - 62976) = i by omega] at hk

theorem minUpTo_124 : ∀ i, i < 64000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 63488
  · exact minUpTo_123 i h
  have hk := mBlock124 (i - 63488) (by omega)
  rwa [show 63488 + (i - 63488) = i by omega] at hk

theorem minUpTo_125 : ∀ i, i < 64512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 64000
  · exact minUpTo_124 i h
  have hk := mBlock125 (i - 64000) (by omega)
  rwa [show 64000 + (i - 64000) = i by omega] at hk

theorem minUpTo_126 : ∀ i, i < 65024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 64512
  · exact minUpTo_125 i h
  have hk := mBlock126 (i - 64512) (by omega)
  rwa [show 64512 + (i - 64512) = i by omega] at hk

theorem minUpTo_127 : ∀ i, i < 65536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 65024
  · exact minUpTo_126 i h
  have hk := mBlock127 (i - 65024) (by omega)
  rwa [show 65024 + (i - 65024) = i by omega] at hk

theorem minUpTo_128 : ∀ i, i < 66048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 65536
  · exact minUpTo_127 i h
  have hk := mBlock128 (i - 65536) (by omega)
  rwa [show 65536 + (i - 65536) = i by omega] at hk

theorem minUpTo_129 : ∀ i, i < 66560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 66048
  · exact minUpTo_128 i h
  have hk := mBlock129 (i - 66048) (by omega)
  rwa [show 66048 + (i - 66048) = i by omega] at hk

theorem minUpTo_130 : ∀ i, i < 67072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 66560
  · exact minUpTo_129 i h
  have hk := mBlock130 (i - 66560) (by omega)
  rwa [show 66560 + (i - 66560) = i by omega] at hk

theorem minUpTo_131 : ∀ i, i < 67584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 67072
  · exact minUpTo_130 i h
  have hk := mBlock131 (i - 67072) (by omega)
  rwa [show 67072 + (i - 67072) = i by omega] at hk

theorem minUpTo_132 : ∀ i, i < 68096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 67584
  · exact minUpTo_131 i h
  have hk := mBlock132 (i - 67584) (by omega)
  rwa [show 67584 + (i - 67584) = i by omega] at hk

theorem minUpTo_133 : ∀ i, i < 68608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 68096
  · exact minUpTo_132 i h
  have hk := mBlock133 (i - 68096) (by omega)
  rwa [show 68096 + (i - 68096) = i by omega] at hk

theorem minUpTo_134 : ∀ i, i < 69120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 68608
  · exact minUpTo_133 i h
  have hk := mBlock134 (i - 68608) (by omega)
  rwa [show 68608 + (i - 68608) = i by omega] at hk

theorem minUpTo_135 : ∀ i, i < 69632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 69120
  · exact minUpTo_134 i h
  have hk := mBlock135 (i - 69120) (by omega)
  rwa [show 69120 + (i - 69120) = i by omega] at hk

theorem minUpTo_136 : ∀ i, i < 70144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 69632
  · exact minUpTo_135 i h
  have hk := mBlock136 (i - 69632) (by omega)
  rwa [show 69632 + (i - 69632) = i by omega] at hk

theorem minUpTo_137 : ∀ i, i < 70656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 70144
  · exact minUpTo_136 i h
  have hk := mBlock137 (i - 70144) (by omega)
  rwa [show 70144 + (i - 70144) = i by omega] at hk

theorem minUpTo_138 : ∀ i, i < 71168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 70656
  · exact minUpTo_137 i h
  have hk := mBlock138 (i - 70656) (by omega)
  rwa [show 70656 + (i - 70656) = i by omega] at hk

theorem minUpTo_139 : ∀ i, i < 71680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 71168
  · exact minUpTo_138 i h
  have hk := mBlock139 (i - 71168) (by omega)
  rwa [show 71168 + (i - 71168) = i by omega] at hk

theorem minUpTo_140 : ∀ i, i < 72192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 71680
  · exact minUpTo_139 i h
  have hk := mBlock140 (i - 71680) (by omega)
  rwa [show 71680 + (i - 71680) = i by omega] at hk

theorem minUpTo_141 : ∀ i, i < 72704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 72192
  · exact minUpTo_140 i h
  have hk := mBlock141 (i - 72192) (by omega)
  rwa [show 72192 + (i - 72192) = i by omega] at hk

theorem minUpTo_142 : ∀ i, i < 73216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 72704
  · exact minUpTo_141 i h
  have hk := mBlock142 (i - 72704) (by omega)
  rwa [show 72704 + (i - 72704) = i by omega] at hk

theorem minUpTo_143 : ∀ i, i < 73728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 73216
  · exact minUpTo_142 i h
  have hk := mBlock143 (i - 73216) (by omega)
  rwa [show 73216 + (i - 73216) = i by omega] at hk

theorem minUpTo_144 : ∀ i, i < 74240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 73728
  · exact minUpTo_143 i h
  have hk := mBlock144 (i - 73728) (by omega)
  rwa [show 73728 + (i - 73728) = i by omega] at hk

theorem minUpTo_145 : ∀ i, i < 74752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 74240
  · exact minUpTo_144 i h
  have hk := mBlock145 (i - 74240) (by omega)
  rwa [show 74240 + (i - 74240) = i by omega] at hk

theorem minUpTo_146 : ∀ i, i < 75264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 74752
  · exact minUpTo_145 i h
  have hk := mBlock146 (i - 74752) (by omega)
  rwa [show 74752 + (i - 74752) = i by omega] at hk

theorem minUpTo_147 : ∀ i, i < 75776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 75264
  · exact minUpTo_146 i h
  have hk := mBlock147 (i - 75264) (by omega)
  rwa [show 75264 + (i - 75264) = i by omega] at hk

theorem minUpTo_148 : ∀ i, i < 76288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 75776
  · exact minUpTo_147 i h
  have hk := mBlock148 (i - 75776) (by omega)
  rwa [show 75776 + (i - 75776) = i by omega] at hk

theorem minUpTo_149 : ∀ i, i < 76800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 76288
  · exact minUpTo_148 i h
  have hk := mBlock149 (i - 76288) (by omega)
  rwa [show 76288 + (i - 76288) = i by omega] at hk

theorem minUpTo_150 : ∀ i, i < 77312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 76800
  · exact minUpTo_149 i h
  have hk := mBlock150 (i - 76800) (by omega)
  rwa [show 76800 + (i - 76800) = i by omega] at hk

theorem minUpTo_151 : ∀ i, i < 77824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 77312
  · exact minUpTo_150 i h
  have hk := mBlock151 (i - 77312) (by omega)
  rwa [show 77312 + (i - 77312) = i by omega] at hk

theorem minUpTo_152 : ∀ i, i < 78336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 77824
  · exact minUpTo_151 i h
  have hk := mBlock152 (i - 77824) (by omega)
  rwa [show 77824 + (i - 77824) = i by omega] at hk

theorem minUpTo_153 : ∀ i, i < 78848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 78336
  · exact minUpTo_152 i h
  have hk := mBlock153 (i - 78336) (by omega)
  rwa [show 78336 + (i - 78336) = i by omega] at hk

theorem minUpTo_154 : ∀ i, i < 79360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 78848
  · exact minUpTo_153 i h
  have hk := mBlock154 (i - 78848) (by omega)
  rwa [show 78848 + (i - 78848) = i by omega] at hk

theorem minUpTo_155 : ∀ i, i < 79872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 79360
  · exact minUpTo_154 i h
  have hk := mBlock155 (i - 79360) (by omega)
  rwa [show 79360 + (i - 79360) = i by omega] at hk

theorem minUpTo_156 : ∀ i, i < 80384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 79872
  · exact minUpTo_155 i h
  have hk := mBlock156 (i - 79872) (by omega)
  rwa [show 79872 + (i - 79872) = i by omega] at hk

theorem minUpTo_157 : ∀ i, i < 80896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 80384
  · exact minUpTo_156 i h
  have hk := mBlock157 (i - 80384) (by omega)
  rwa [show 80384 + (i - 80384) = i by omega] at hk

theorem minUpTo_158 : ∀ i, i < 81408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 80896
  · exact minUpTo_157 i h
  have hk := mBlock158 (i - 80896) (by omega)
  rwa [show 80896 + (i - 80896) = i by omega] at hk

theorem minUpTo_159 : ∀ i, i < 81920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 81408
  · exact minUpTo_158 i h
  have hk := mBlock159 (i - 81408) (by omega)
  rwa [show 81408 + (i - 81408) = i by omega] at hk

theorem minUpTo_160 : ∀ i, i < 82432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 81920
  · exact minUpTo_159 i h
  have hk := mBlock160 (i - 81920) (by omega)
  rwa [show 81920 + (i - 81920) = i by omega] at hk

theorem minUpTo_161 : ∀ i, i < 82944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 82432
  · exact minUpTo_160 i h
  have hk := mBlock161 (i - 82432) (by omega)
  rwa [show 82432 + (i - 82432) = i by omega] at hk

theorem minUpTo_162 : ∀ i, i < 83456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 82944
  · exact minUpTo_161 i h
  have hk := mBlock162 (i - 82944) (by omega)
  rwa [show 82944 + (i - 82944) = i by omega] at hk

theorem minUpTo_163 : ∀ i, i < 83968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 83456
  · exact minUpTo_162 i h
  have hk := mBlock163 (i - 83456) (by omega)
  rwa [show 83456 + (i - 83456) = i by omega] at hk

theorem minUpTo_164 : ∀ i, i < 84480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 83968
  · exact minUpTo_163 i h
  have hk := mBlock164 (i - 83968) (by omega)
  rwa [show 83968 + (i - 83968) = i by omega] at hk

theorem minUpTo_165 : ∀ i, i < 84992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 84480
  · exact minUpTo_164 i h
  have hk := mBlock165 (i - 84480) (by omega)
  rwa [show 84480 + (i - 84480) = i by omega] at hk

theorem minUpTo_166 : ∀ i, i < 85504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 84992
  · exact minUpTo_165 i h
  have hk := mBlock166 (i - 84992) (by omega)
  rwa [show 84992 + (i - 84992) = i by omega] at hk

theorem minUpTo_167 : ∀ i, i < 86016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 85504
  · exact minUpTo_166 i h
  have hk := mBlock167 (i - 85504) (by omega)
  rwa [show 85504 + (i - 85504) = i by omega] at hk

theorem minUpTo_168 : ∀ i, i < 86528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 86016
  · exact minUpTo_167 i h
  have hk := mBlock168 (i - 86016) (by omega)
  rwa [show 86016 + (i - 86016) = i by omega] at hk

theorem minUpTo_169 : ∀ i, i < 87040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 86528
  · exact minUpTo_168 i h
  have hk := mBlock169 (i - 86528) (by omega)
  rwa [show 86528 + (i - 86528) = i by omega] at hk

theorem minUpTo_170 : ∀ i, i < 87552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 87040
  · exact minUpTo_169 i h
  have hk := mBlock170 (i - 87040) (by omega)
  rwa [show 87040 + (i - 87040) = i by omega] at hk

theorem minUpTo_171 : ∀ i, i < 88064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 87552
  · exact minUpTo_170 i h
  have hk := mBlock171 (i - 87552) (by omega)
  rwa [show 87552 + (i - 87552) = i by omega] at hk

theorem minUpTo_172 : ∀ i, i < 88576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 88064
  · exact minUpTo_171 i h
  have hk := mBlock172 (i - 88064) (by omega)
  rwa [show 88064 + (i - 88064) = i by omega] at hk

theorem minUpTo_173 : ∀ i, i < 89088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 88576
  · exact minUpTo_172 i h
  have hk := mBlock173 (i - 88576) (by omega)
  rwa [show 88576 + (i - 88576) = i by omega] at hk

theorem minUpTo_174 : ∀ i, i < 89600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 89088
  · exact minUpTo_173 i h
  have hk := mBlock174 (i - 89088) (by omega)
  rwa [show 89088 + (i - 89088) = i by omega] at hk

theorem minUpTo_175 : ∀ i, i < 90112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 89600
  · exact minUpTo_174 i h
  have hk := mBlock175 (i - 89600) (by omega)
  rwa [show 89600 + (i - 89600) = i by omega] at hk

theorem minUpTo_176 : ∀ i, i < 90624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 90112
  · exact minUpTo_175 i h
  have hk := mBlock176 (i - 90112) (by omega)
  rwa [show 90112 + (i - 90112) = i by omega] at hk

theorem minUpTo_177 : ∀ i, i < 91136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 90624
  · exact minUpTo_176 i h
  have hk := mBlock177 (i - 90624) (by omega)
  rwa [show 90624 + (i - 90624) = i by omega] at hk

theorem minUpTo_178 : ∀ i, i < 91648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 91136
  · exact minUpTo_177 i h
  have hk := mBlock178 (i - 91136) (by omega)
  rwa [show 91136 + (i - 91136) = i by omega] at hk

theorem minUpTo_179 : ∀ i, i < 92160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 91648
  · exact minUpTo_178 i h
  have hk := mBlock179 (i - 91648) (by omega)
  rwa [show 91648 + (i - 91648) = i by omega] at hk

theorem minUpTo_180 : ∀ i, i < 92672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 92160
  · exact minUpTo_179 i h
  have hk := mBlock180 (i - 92160) (by omega)
  rwa [show 92160 + (i - 92160) = i by omega] at hk

theorem minUpTo_181 : ∀ i, i < 93184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 92672
  · exact minUpTo_180 i h
  have hk := mBlock181 (i - 92672) (by omega)
  rwa [show 92672 + (i - 92672) = i by omega] at hk

theorem minUpTo_182 : ∀ i, i < 93696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 93184
  · exact minUpTo_181 i h
  have hk := mBlock182 (i - 93184) (by omega)
  rwa [show 93184 + (i - 93184) = i by omega] at hk

theorem minUpTo_183 : ∀ i, i < 94208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 93696
  · exact minUpTo_182 i h
  have hk := mBlock183 (i - 93696) (by omega)
  rwa [show 93696 + (i - 93696) = i by omega] at hk

theorem minUpTo_184 : ∀ i, i < 94720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 94208
  · exact minUpTo_183 i h
  have hk := mBlock184 (i - 94208) (by omega)
  rwa [show 94208 + (i - 94208) = i by omega] at hk

theorem minUpTo_185 : ∀ i, i < 95232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 94720
  · exact minUpTo_184 i h
  have hk := mBlock185 (i - 94720) (by omega)
  rwa [show 94720 + (i - 94720) = i by omega] at hk

theorem minUpTo_186 : ∀ i, i < 95744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 95232
  · exact minUpTo_185 i h
  have hk := mBlock186 (i - 95232) (by omega)
  rwa [show 95232 + (i - 95232) = i by omega] at hk

theorem minUpTo_187 : ∀ i, i < 96256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 95744
  · exact minUpTo_186 i h
  have hk := mBlock187 (i - 95744) (by omega)
  rwa [show 95744 + (i - 95744) = i by omega] at hk

theorem minUpTo_188 : ∀ i, i < 96768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 96256
  · exact minUpTo_187 i h
  have hk := mBlock188 (i - 96256) (by omega)
  rwa [show 96256 + (i - 96256) = i by omega] at hk

theorem minUpTo_189 : ∀ i, i < 97280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 96768
  · exact minUpTo_188 i h
  have hk := mBlock189 (i - 96768) (by omega)
  rwa [show 96768 + (i - 96768) = i by omega] at hk

theorem minUpTo_190 : ∀ i, i < 97792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 97280
  · exact minUpTo_189 i h
  have hk := mBlock190 (i - 97280) (by omega)
  rwa [show 97280 + (i - 97280) = i by omega] at hk

theorem minUpTo_191 : ∀ i, i < 98304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 97792
  · exact minUpTo_190 i h
  have hk := mBlock191 (i - 97792) (by omega)
  rwa [show 97792 + (i - 97792) = i by omega] at hk

theorem minUpTo_192 : ∀ i, i < 98816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 98304
  · exact minUpTo_191 i h
  have hk := mBlock192 (i - 98304) (by omega)
  rwa [show 98304 + (i - 98304) = i by omega] at hk

theorem minUpTo_193 : ∀ i, i < 99328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 98816
  · exact minUpTo_192 i h
  have hk := mBlock193 (i - 98816) (by omega)
  rwa [show 98816 + (i - 98816) = i by omega] at hk

theorem minUpTo_194 : ∀ i, i < 99840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 99328
  · exact minUpTo_193 i h
  have hk := mBlock194 (i - 99328) (by omega)
  rwa [show 99328 + (i - 99328) = i by omega] at hk

theorem minUpTo_195 : ∀ i, i < 100352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 99840
  · exact minUpTo_194 i h
  have hk := mBlock195 (i - 99840) (by omega)
  rwa [show 99840 + (i - 99840) = i by omega] at hk

theorem minUpTo_196 : ∀ i, i < 100864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 100352
  · exact minUpTo_195 i h
  have hk := mBlock196 (i - 100352) (by omega)
  rwa [show 100352 + (i - 100352) = i by omega] at hk

theorem minUpTo_197 : ∀ i, i < 101376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 100864
  · exact minUpTo_196 i h
  have hk := mBlock197 (i - 100864) (by omega)
  rwa [show 100864 + (i - 100864) = i by omega] at hk

theorem minUpTo_198 : ∀ i, i < 101888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 101376
  · exact minUpTo_197 i h
  have hk := mBlock198 (i - 101376) (by omega)
  rwa [show 101376 + (i - 101376) = i by omega] at hk

theorem minUpTo_199 : ∀ i, i < 102400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 101888
  · exact minUpTo_198 i h
  have hk := mBlock199 (i - 101888) (by omega)
  rwa [show 101888 + (i - 101888) = i by omega] at hk

theorem minUpTo_200 : ∀ i, i < 102912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 102400
  · exact minUpTo_199 i h
  have hk := mBlock200 (i - 102400) (by omega)
  rwa [show 102400 + (i - 102400) = i by omega] at hk

theorem minUpTo_201 : ∀ i, i < 103424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 102912
  · exact minUpTo_200 i h
  have hk := mBlock201 (i - 102912) (by omega)
  rwa [show 102912 + (i - 102912) = i by omega] at hk

theorem minUpTo_202 : ∀ i, i < 103936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 103424
  · exact minUpTo_201 i h
  have hk := mBlock202 (i - 103424) (by omega)
  rwa [show 103424 + (i - 103424) = i by omega] at hk

theorem minUpTo_203 : ∀ i, i < 104448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 103936
  · exact minUpTo_202 i h
  have hk := mBlock203 (i - 103936) (by omega)
  rwa [show 103936 + (i - 103936) = i by omega] at hk

theorem minUpTo_204 : ∀ i, i < 104960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 104448
  · exact minUpTo_203 i h
  have hk := mBlock204 (i - 104448) (by omega)
  rwa [show 104448 + (i - 104448) = i by omega] at hk

theorem minUpTo_205 : ∀ i, i < 105472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 104960
  · exact minUpTo_204 i h
  have hk := mBlock205 (i - 104960) (by omega)
  rwa [show 104960 + (i - 104960) = i by omega] at hk

theorem minUpTo_206 : ∀ i, i < 105984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 105472
  · exact minUpTo_205 i h
  have hk := mBlock206 (i - 105472) (by omega)
  rwa [show 105472 + (i - 105472) = i by omega] at hk

theorem minUpTo_207 : ∀ i, i < 106496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 105984
  · exact minUpTo_206 i h
  have hk := mBlock207 (i - 105984) (by omega)
  rwa [show 105984 + (i - 105984) = i by omega] at hk

theorem minUpTo_208 : ∀ i, i < 107008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 106496
  · exact minUpTo_207 i h
  have hk := mBlock208 (i - 106496) (by omega)
  rwa [show 106496 + (i - 106496) = i by omega] at hk

theorem minUpTo_209 : ∀ i, i < 107520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 107008
  · exact minUpTo_208 i h
  have hk := mBlock209 (i - 107008) (by omega)
  rwa [show 107008 + (i - 107008) = i by omega] at hk

theorem minUpTo_210 : ∀ i, i < 108032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 107520
  · exact minUpTo_209 i h
  have hk := mBlock210 (i - 107520) (by omega)
  rwa [show 107520 + (i - 107520) = i by omega] at hk

theorem minUpTo_211 : ∀ i, i < 108544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 108032
  · exact minUpTo_210 i h
  have hk := mBlock211 (i - 108032) (by omega)
  rwa [show 108032 + (i - 108032) = i by omega] at hk

theorem minUpTo_212 : ∀ i, i < 109056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 108544
  · exact minUpTo_211 i h
  have hk := mBlock212 (i - 108544) (by omega)
  rwa [show 108544 + (i - 108544) = i by omega] at hk

theorem minUpTo_213 : ∀ i, i < 109568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 109056
  · exact minUpTo_212 i h
  have hk := mBlock213 (i - 109056) (by omega)
  rwa [show 109056 + (i - 109056) = i by omega] at hk

theorem minUpTo_214 : ∀ i, i < 110080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 109568
  · exact minUpTo_213 i h
  have hk := mBlock214 (i - 109568) (by omega)
  rwa [show 109568 + (i - 109568) = i by omega] at hk

theorem minUpTo_215 : ∀ i, i < 110592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 110080
  · exact minUpTo_214 i h
  have hk := mBlock215 (i - 110080) (by omega)
  rwa [show 110080 + (i - 110080) = i by omega] at hk

theorem minUpTo_216 : ∀ i, i < 111104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 110592
  · exact minUpTo_215 i h
  have hk := mBlock216 (i - 110592) (by omega)
  rwa [show 110592 + (i - 110592) = i by omega] at hk

theorem minUpTo_217 : ∀ i, i < 111616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 111104
  · exact minUpTo_216 i h
  have hk := mBlock217 (i - 111104) (by omega)
  rwa [show 111104 + (i - 111104) = i by omega] at hk

theorem minUpTo_218 : ∀ i, i < 112128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 111616
  · exact minUpTo_217 i h
  have hk := mBlock218 (i - 111616) (by omega)
  rwa [show 111616 + (i - 111616) = i by omega] at hk

theorem minUpTo_219 : ∀ i, i < 112640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 112128
  · exact minUpTo_218 i h
  have hk := mBlock219 (i - 112128) (by omega)
  rwa [show 112128 + (i - 112128) = i by omega] at hk

theorem minUpTo_220 : ∀ i, i < 113152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 112640
  · exact minUpTo_219 i h
  have hk := mBlock220 (i - 112640) (by omega)
  rwa [show 112640 + (i - 112640) = i by omega] at hk

theorem minUpTo_221 : ∀ i, i < 113664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 113152
  · exact minUpTo_220 i h
  have hk := mBlock221 (i - 113152) (by omega)
  rwa [show 113152 + (i - 113152) = i by omega] at hk

theorem minUpTo_222 : ∀ i, i < 114176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 113664
  · exact minUpTo_221 i h
  have hk := mBlock222 (i - 113664) (by omega)
  rwa [show 113664 + (i - 113664) = i by omega] at hk

theorem minUpTo_223 : ∀ i, i < 114688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 114176
  · exact minUpTo_222 i h
  have hk := mBlock223 (i - 114176) (by omega)
  rwa [show 114176 + (i - 114176) = i by omega] at hk

theorem minUpTo_224 : ∀ i, i < 115200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 114688
  · exact minUpTo_223 i h
  have hk := mBlock224 (i - 114688) (by omega)
  rwa [show 114688 + (i - 114688) = i by omega] at hk

theorem minUpTo_225 : ∀ i, i < 115712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 115200
  · exact minUpTo_224 i h
  have hk := mBlock225 (i - 115200) (by omega)
  rwa [show 115200 + (i - 115200) = i by omega] at hk

theorem minUpTo_226 : ∀ i, i < 116224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 115712
  · exact minUpTo_225 i h
  have hk := mBlock226 (i - 115712) (by omega)
  rwa [show 115712 + (i - 115712) = i by omega] at hk

theorem minUpTo_227 : ∀ i, i < 116736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 116224
  · exact minUpTo_226 i h
  have hk := mBlock227 (i - 116224) (by omega)
  rwa [show 116224 + (i - 116224) = i by omega] at hk

theorem minUpTo_228 : ∀ i, i < 117248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 116736
  · exact minUpTo_227 i h
  have hk := mBlock228 (i - 116736) (by omega)
  rwa [show 116736 + (i - 116736) = i by omega] at hk

theorem minUpTo_229 : ∀ i, i < 117760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 117248
  · exact minUpTo_228 i h
  have hk := mBlock229 (i - 117248) (by omega)
  rwa [show 117248 + (i - 117248) = i by omega] at hk

theorem minUpTo_230 : ∀ i, i < 118272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 117760
  · exact minUpTo_229 i h
  have hk := mBlock230 (i - 117760) (by omega)
  rwa [show 117760 + (i - 117760) = i by omega] at hk

theorem minUpTo_231 : ∀ i, i < 118784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 118272
  · exact minUpTo_230 i h
  have hk := mBlock231 (i - 118272) (by omega)
  rwa [show 118272 + (i - 118272) = i by omega] at hk

theorem minUpTo_232 : ∀ i, i < 119296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 118784
  · exact minUpTo_231 i h
  have hk := mBlock232 (i - 118784) (by omega)
  rwa [show 118784 + (i - 118784) = i by omega] at hk

theorem minUpTo_233 : ∀ i, i < 119808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 119296
  · exact minUpTo_232 i h
  have hk := mBlock233 (i - 119296) (by omega)
  rwa [show 119296 + (i - 119296) = i by omega] at hk

theorem minUpTo_234 : ∀ i, i < 120320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 119808
  · exact minUpTo_233 i h
  have hk := mBlock234 (i - 119808) (by omega)
  rwa [show 119808 + (i - 119808) = i by omega] at hk

theorem minUpTo_235 : ∀ i, i < 120832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 120320
  · exact minUpTo_234 i h
  have hk := mBlock235 (i - 120320) (by omega)
  rwa [show 120320 + (i - 120320) = i by omega] at hk

theorem minUpTo_236 : ∀ i, i < 121344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 120832
  · exact minUpTo_235 i h
  have hk := mBlock236 (i - 120832) (by omega)
  rwa [show 120832 + (i - 120832) = i by omega] at hk

theorem minUpTo_237 : ∀ i, i < 121856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 121344
  · exact minUpTo_236 i h
  have hk := mBlock237 (i - 121344) (by omega)
  rwa [show 121344 + (i - 121344) = i by omega] at hk

theorem minUpTo_238 : ∀ i, i < 122368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 121856
  · exact minUpTo_237 i h
  have hk := mBlock238 (i - 121856) (by omega)
  rwa [show 121856 + (i - 121856) = i by omega] at hk

theorem minUpTo_239 : ∀ i, i < 122880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 122368
  · exact minUpTo_238 i h
  have hk := mBlock239 (i - 122368) (by omega)
  rwa [show 122368 + (i - 122368) = i by omega] at hk

theorem minUpTo_240 : ∀ i, i < 123392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 122880
  · exact minUpTo_239 i h
  have hk := mBlock240 (i - 122880) (by omega)
  rwa [show 122880 + (i - 122880) = i by omega] at hk

theorem minUpTo_241 : ∀ i, i < 123904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 123392
  · exact minUpTo_240 i h
  have hk := mBlock241 (i - 123392) (by omega)
  rwa [show 123392 + (i - 123392) = i by omega] at hk

theorem minUpTo_242 : ∀ i, i < 124416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 123904
  · exact minUpTo_241 i h
  have hk := mBlock242 (i - 123904) (by omega)
  rwa [show 123904 + (i - 123904) = i by omega] at hk

theorem minUpTo_243 : ∀ i, i < 124928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 124416
  · exact minUpTo_242 i h
  have hk := mBlock243 (i - 124416) (by omega)
  rwa [show 124416 + (i - 124416) = i by omega] at hk

theorem minUpTo_244 : ∀ i, i < 125440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 124928
  · exact minUpTo_243 i h
  have hk := mBlock244 (i - 124928) (by omega)
  rwa [show 124928 + (i - 124928) = i by omega] at hk

theorem minUpTo_245 : ∀ i, i < 125952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 125440
  · exact minUpTo_244 i h
  have hk := mBlock245 (i - 125440) (by omega)
  rwa [show 125440 + (i - 125440) = i by omega] at hk

theorem minUpTo_246 : ∀ i, i < 126464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 125952
  · exact minUpTo_245 i h
  have hk := mBlock246 (i - 125952) (by omega)
  rwa [show 125952 + (i - 125952) = i by omega] at hk

theorem minUpTo_247 : ∀ i, i < 126976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 126464
  · exact minUpTo_246 i h
  have hk := mBlock247 (i - 126464) (by omega)
  rwa [show 126464 + (i - 126464) = i by omega] at hk

theorem minUpTo_248 : ∀ i, i < 127488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 126976
  · exact minUpTo_247 i h
  have hk := mBlock248 (i - 126976) (by omega)
  rwa [show 126976 + (i - 126976) = i by omega] at hk

theorem minUpTo_249 : ∀ i, i < 128000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 127488
  · exact minUpTo_248 i h
  have hk := mBlock249 (i - 127488) (by omega)
  rwa [show 127488 + (i - 127488) = i by omega] at hk

theorem minUpTo_250 : ∀ i, i < 128512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 128000
  · exact minUpTo_249 i h
  have hk := mBlock250 (i - 128000) (by omega)
  rwa [show 128000 + (i - 128000) = i by omega] at hk

theorem minUpTo_251 : ∀ i, i < 129024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 128512
  · exact minUpTo_250 i h
  have hk := mBlock251 (i - 128512) (by omega)
  rwa [show 128512 + (i - 128512) = i by omega] at hk

theorem minUpTo_252 : ∀ i, i < 129536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 129024
  · exact minUpTo_251 i h
  have hk := mBlock252 (i - 129024) (by omega)
  rwa [show 129024 + (i - 129024) = i by omega] at hk

theorem minUpTo_253 : ∀ i, i < 130048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 129536
  · exact minUpTo_252 i h
  have hk := mBlock253 (i - 129536) (by omega)
  rwa [show 129536 + (i - 129536) = i by omega] at hk

theorem minUpTo_254 : ∀ i, i < 130560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 130048
  · exact minUpTo_253 i h
  have hk := mBlock254 (i - 130048) (by omega)
  rwa [show 130048 + (i - 130048) = i by omega] at hk

theorem minUpTo_255 : ∀ i, i < 131072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 130560
  · exact minUpTo_254 i h
  have hk := mBlock255 (i - 130560) (by omega)
  rwa [show 130560 + (i - 130560) = i by omega] at hk

theorem minUpTo_256 : ∀ i, i < 131584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 131072
  · exact minUpTo_255 i h
  have hk := mBlock256 (i - 131072) (by omega)
  rwa [show 131072 + (i - 131072) = i by omega] at hk

theorem minUpTo_257 : ∀ i, i < 132096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 131584
  · exact minUpTo_256 i h
  have hk := mBlock257 (i - 131584) (by omega)
  rwa [show 131584 + (i - 131584) = i by omega] at hk

theorem minUpTo_258 : ∀ i, i < 132608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 132096
  · exact minUpTo_257 i h
  have hk := mBlock258 (i - 132096) (by omega)
  rwa [show 132096 + (i - 132096) = i by omega] at hk

theorem minUpTo_259 : ∀ i, i < 133120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 132608
  · exact minUpTo_258 i h
  have hk := mBlock259 (i - 132608) (by omega)
  rwa [show 132608 + (i - 132608) = i by omega] at hk

theorem minUpTo_260 : ∀ i, i < 133632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 133120
  · exact minUpTo_259 i h
  have hk := mBlock260 (i - 133120) (by omega)
  rwa [show 133120 + (i - 133120) = i by omega] at hk

theorem minUpTo_261 : ∀ i, i < 134144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 133632
  · exact minUpTo_260 i h
  have hk := mBlock261 (i - 133632) (by omega)
  rwa [show 133632 + (i - 133632) = i by omega] at hk

theorem minUpTo_262 : ∀ i, i < 134656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 134144
  · exact minUpTo_261 i h
  have hk := mBlock262 (i - 134144) (by omega)
  rwa [show 134144 + (i - 134144) = i by omega] at hk

theorem minUpTo_263 : ∀ i, i < 135168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 134656
  · exact minUpTo_262 i h
  have hk := mBlock263 (i - 134656) (by omega)
  rwa [show 134656 + (i - 134656) = i by omega] at hk

theorem minUpTo_264 : ∀ i, i < 135680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 135168
  · exact minUpTo_263 i h
  have hk := mBlock264 (i - 135168) (by omega)
  rwa [show 135168 + (i - 135168) = i by omega] at hk

theorem minUpTo_265 : ∀ i, i < 136192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 135680
  · exact minUpTo_264 i h
  have hk := mBlock265 (i - 135680) (by omega)
  rwa [show 135680 + (i - 135680) = i by omega] at hk

theorem minUpTo_266 : ∀ i, i < 136704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 136192
  · exact minUpTo_265 i h
  have hk := mBlock266 (i - 136192) (by omega)
  rwa [show 136192 + (i - 136192) = i by omega] at hk

theorem minUpTo_267 : ∀ i, i < 137216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 136704
  · exact minUpTo_266 i h
  have hk := mBlock267 (i - 136704) (by omega)
  rwa [show 136704 + (i - 136704) = i by omega] at hk

theorem minUpTo_268 : ∀ i, i < 137728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 137216
  · exact minUpTo_267 i h
  have hk := mBlock268 (i - 137216) (by omega)
  rwa [show 137216 + (i - 137216) = i by omega] at hk

theorem minUpTo_269 : ∀ i, i < 138240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 137728
  · exact minUpTo_268 i h
  have hk := mBlock269 (i - 137728) (by omega)
  rwa [show 137728 + (i - 137728) = i by omega] at hk

theorem minUpTo_270 : ∀ i, i < 138752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 138240
  · exact minUpTo_269 i h
  have hk := mBlock270 (i - 138240) (by omega)
  rwa [show 138240 + (i - 138240) = i by omega] at hk

theorem minUpTo_271 : ∀ i, i < 139264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 138752
  · exact minUpTo_270 i h
  have hk := mBlock271 (i - 138752) (by omega)
  rwa [show 138752 + (i - 138752) = i by omega] at hk

theorem minUpTo_272 : ∀ i, i < 139776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 139264
  · exact minUpTo_271 i h
  have hk := mBlock272 (i - 139264) (by omega)
  rwa [show 139264 + (i - 139264) = i by omega] at hk

theorem minUpTo_273 : ∀ i, i < 140288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 139776
  · exact minUpTo_272 i h
  have hk := mBlock273 (i - 139776) (by omega)
  rwa [show 139776 + (i - 139776) = i by omega] at hk

theorem minUpTo_274 : ∀ i, i < 140800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 140288
  · exact minUpTo_273 i h
  have hk := mBlock274 (i - 140288) (by omega)
  rwa [show 140288 + (i - 140288) = i by omega] at hk

theorem minUpTo_275 : ∀ i, i < 141312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 140800
  · exact minUpTo_274 i h
  have hk := mBlock275 (i - 140800) (by omega)
  rwa [show 140800 + (i - 140800) = i by omega] at hk

theorem minUpTo_276 : ∀ i, i < 141824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 141312
  · exact minUpTo_275 i h
  have hk := mBlock276 (i - 141312) (by omega)
  rwa [show 141312 + (i - 141312) = i by omega] at hk

theorem minUpTo_277 : ∀ i, i < 142336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 141824
  · exact minUpTo_276 i h
  have hk := mBlock277 (i - 141824) (by omega)
  rwa [show 141824 + (i - 141824) = i by omega] at hk

theorem minUpTo_278 : ∀ i, i < 142848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 142336
  · exact minUpTo_277 i h
  have hk := mBlock278 (i - 142336) (by omega)
  rwa [show 142336 + (i - 142336) = i by omega] at hk

theorem minUpTo_279 : ∀ i, i < 143360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 142848
  · exact minUpTo_278 i h
  have hk := mBlock279 (i - 142848) (by omega)
  rwa [show 142848 + (i - 142848) = i by omega] at hk

theorem minUpTo_280 : ∀ i, i < 143872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 143360
  · exact minUpTo_279 i h
  have hk := mBlock280 (i - 143360) (by omega)
  rwa [show 143360 + (i - 143360) = i by omega] at hk

theorem minUpTo_281 : ∀ i, i < 144384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 143872
  · exact minUpTo_280 i h
  have hk := mBlock281 (i - 143872) (by omega)
  rwa [show 143872 + (i - 143872) = i by omega] at hk

theorem minUpTo_282 : ∀ i, i < 144896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 144384
  · exact minUpTo_281 i h
  have hk := mBlock282 (i - 144384) (by omega)
  rwa [show 144384 + (i - 144384) = i by omega] at hk

theorem minUpTo_283 : ∀ i, i < 145408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 144896
  · exact minUpTo_282 i h
  have hk := mBlock283 (i - 144896) (by omega)
  rwa [show 144896 + (i - 144896) = i by omega] at hk

theorem minUpTo_284 : ∀ i, i < 145920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 145408
  · exact minUpTo_283 i h
  have hk := mBlock284 (i - 145408) (by omega)
  rwa [show 145408 + (i - 145408) = i by omega] at hk

theorem minUpTo_285 : ∀ i, i < 146432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 145920
  · exact minUpTo_284 i h
  have hk := mBlock285 (i - 145920) (by omega)
  rwa [show 145920 + (i - 145920) = i by omega] at hk

theorem minUpTo_286 : ∀ i, i < 146944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 146432
  · exact minUpTo_285 i h
  have hk := mBlock286 (i - 146432) (by omega)
  rwa [show 146432 + (i - 146432) = i by omega] at hk

theorem minUpTo_287 : ∀ i, i < 147456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 146944
  · exact minUpTo_286 i h
  have hk := mBlock287 (i - 146944) (by omega)
  rwa [show 146944 + (i - 146944) = i by omega] at hk

theorem minUpTo_288 : ∀ i, i < 147968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 147456
  · exact minUpTo_287 i h
  have hk := mBlock288 (i - 147456) (by omega)
  rwa [show 147456 + (i - 147456) = i by omega] at hk

theorem minUpTo_289 : ∀ i, i < 148480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 147968
  · exact minUpTo_288 i h
  have hk := mBlock289 (i - 147968) (by omega)
  rwa [show 147968 + (i - 147968) = i by omega] at hk

theorem minUpTo_290 : ∀ i, i < 148992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 148480
  · exact minUpTo_289 i h
  have hk := mBlock290 (i - 148480) (by omega)
  rwa [show 148480 + (i - 148480) = i by omega] at hk

theorem minUpTo_291 : ∀ i, i < 149504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 148992
  · exact minUpTo_290 i h
  have hk := mBlock291 (i - 148992) (by omega)
  rwa [show 148992 + (i - 148992) = i by omega] at hk

theorem minUpTo_292 : ∀ i, i < 150016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 149504
  · exact minUpTo_291 i h
  have hk := mBlock292 (i - 149504) (by omega)
  rwa [show 149504 + (i - 149504) = i by omega] at hk

theorem minUpTo_293 : ∀ i, i < 150528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 150016
  · exact minUpTo_292 i h
  have hk := mBlock293 (i - 150016) (by omega)
  rwa [show 150016 + (i - 150016) = i by omega] at hk

theorem minUpTo_294 : ∀ i, i < 151040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 150528
  · exact minUpTo_293 i h
  have hk := mBlock294 (i - 150528) (by omega)
  rwa [show 150528 + (i - 150528) = i by omega] at hk

theorem minUpTo_295 : ∀ i, i < 151552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 151040
  · exact minUpTo_294 i h
  have hk := mBlock295 (i - 151040) (by omega)
  rwa [show 151040 + (i - 151040) = i by omega] at hk

theorem minUpTo_296 : ∀ i, i < 152064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 151552
  · exact minUpTo_295 i h
  have hk := mBlock296 (i - 151552) (by omega)
  rwa [show 151552 + (i - 151552) = i by omega] at hk

theorem minUpTo_297 : ∀ i, i < 152576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 152064
  · exact minUpTo_296 i h
  have hk := mBlock297 (i - 152064) (by omega)
  rwa [show 152064 + (i - 152064) = i by omega] at hk

theorem minUpTo_298 : ∀ i, i < 153088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 152576
  · exact minUpTo_297 i h
  have hk := mBlock298 (i - 152576) (by omega)
  rwa [show 152576 + (i - 152576) = i by omega] at hk

theorem minUpTo_299 : ∀ i, i < 153600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 153088
  · exact minUpTo_298 i h
  have hk := mBlock299 (i - 153088) (by omega)
  rwa [show 153088 + (i - 153088) = i by omega] at hk

theorem minUpTo_300 : ∀ i, i < 154112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 153600
  · exact minUpTo_299 i h
  have hk := mBlock300 (i - 153600) (by omega)
  rwa [show 153600 + (i - 153600) = i by omega] at hk

theorem minUpTo_301 : ∀ i, i < 154624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 154112
  · exact minUpTo_300 i h
  have hk := mBlock301 (i - 154112) (by omega)
  rwa [show 154112 + (i - 154112) = i by omega] at hk

theorem minUpTo_302 : ∀ i, i < 155136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 154624
  · exact minUpTo_301 i h
  have hk := mBlock302 (i - 154624) (by omega)
  rwa [show 154624 + (i - 154624) = i by omega] at hk

theorem minUpTo_303 : ∀ i, i < 155648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 155136
  · exact minUpTo_302 i h
  have hk := mBlock303 (i - 155136) (by omega)
  rwa [show 155136 + (i - 155136) = i by omega] at hk

theorem minUpTo_304 : ∀ i, i < 156160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 155648
  · exact minUpTo_303 i h
  have hk := mBlock304 (i - 155648) (by omega)
  rwa [show 155648 + (i - 155648) = i by omega] at hk

theorem minUpTo_305 : ∀ i, i < 156672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 156160
  · exact minUpTo_304 i h
  have hk := mBlock305 (i - 156160) (by omega)
  rwa [show 156160 + (i - 156160) = i by omega] at hk

theorem minUpTo_306 : ∀ i, i < 157184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 156672
  · exact minUpTo_305 i h
  have hk := mBlock306 (i - 156672) (by omega)
  rwa [show 156672 + (i - 156672) = i by omega] at hk

theorem minUpTo_307 : ∀ i, i < 157696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 157184
  · exact minUpTo_306 i h
  have hk := mBlock307 (i - 157184) (by omega)
  rwa [show 157184 + (i - 157184) = i by omega] at hk

theorem minUpTo_308 : ∀ i, i < 158208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 157696
  · exact minUpTo_307 i h
  have hk := mBlock308 (i - 157696) (by omega)
  rwa [show 157696 + (i - 157696) = i by omega] at hk

theorem minUpTo_309 : ∀ i, i < 158720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 158208
  · exact minUpTo_308 i h
  have hk := mBlock309 (i - 158208) (by omega)
  rwa [show 158208 + (i - 158208) = i by omega] at hk

theorem minUpTo_310 : ∀ i, i < 159232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 158720
  · exact minUpTo_309 i h
  have hk := mBlock310 (i - 158720) (by omega)
  rwa [show 158720 + (i - 158720) = i by omega] at hk

theorem minUpTo_311 : ∀ i, i < 159744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 159232
  · exact minUpTo_310 i h
  have hk := mBlock311 (i - 159232) (by omega)
  rwa [show 159232 + (i - 159232) = i by omega] at hk

theorem minUpTo_312 : ∀ i, i < 160256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 159744
  · exact minUpTo_311 i h
  have hk := mBlock312 (i - 159744) (by omega)
  rwa [show 159744 + (i - 159744) = i by omega] at hk

theorem minUpTo_313 : ∀ i, i < 160768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 160256
  · exact minUpTo_312 i h
  have hk := mBlock313 (i - 160256) (by omega)
  rwa [show 160256 + (i - 160256) = i by omega] at hk

theorem minUpTo_314 : ∀ i, i < 161280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 160768
  · exact minUpTo_313 i h
  have hk := mBlock314 (i - 160768) (by omega)
  rwa [show 160768 + (i - 160768) = i by omega] at hk

theorem minUpTo_315 : ∀ i, i < 161792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 161280
  · exact minUpTo_314 i h
  have hk := mBlock315 (i - 161280) (by omega)
  rwa [show 161280 + (i - 161280) = i by omega] at hk

theorem minUpTo_316 : ∀ i, i < 162304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 161792
  · exact minUpTo_315 i h
  have hk := mBlock316 (i - 161792) (by omega)
  rwa [show 161792 + (i - 161792) = i by omega] at hk

theorem minUpTo_317 : ∀ i, i < 162816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 162304
  · exact minUpTo_316 i h
  have hk := mBlock317 (i - 162304) (by omega)
  rwa [show 162304 + (i - 162304) = i by omega] at hk

theorem minUpTo_318 : ∀ i, i < 163328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 162816
  · exact minUpTo_317 i h
  have hk := mBlock318 (i - 162816) (by omega)
  rwa [show 162816 + (i - 162816) = i by omega] at hk

theorem minUpTo_319 : ∀ i, i < 163840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 163328
  · exact minUpTo_318 i h
  have hk := mBlock319 (i - 163328) (by omega)
  rwa [show 163328 + (i - 163328) = i by omega] at hk

theorem minUpTo_320 : ∀ i, i < 164352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 163840
  · exact minUpTo_319 i h
  have hk := mBlock320 (i - 163840) (by omega)
  rwa [show 163840 + (i - 163840) = i by omega] at hk

theorem minUpTo_321 : ∀ i, i < 164864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 164352
  · exact minUpTo_320 i h
  have hk := mBlock321 (i - 164352) (by omega)
  rwa [show 164352 + (i - 164352) = i by omega] at hk

theorem minUpTo_322 : ∀ i, i < 165376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 164864
  · exact minUpTo_321 i h
  have hk := mBlock322 (i - 164864) (by omega)
  rwa [show 164864 + (i - 164864) = i by omega] at hk

theorem minUpTo_323 : ∀ i, i < 165888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 165376
  · exact minUpTo_322 i h
  have hk := mBlock323 (i - 165376) (by omega)
  rwa [show 165376 + (i - 165376) = i by omega] at hk

theorem minUpTo_324 : ∀ i, i < 166400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 165888
  · exact minUpTo_323 i h
  have hk := mBlock324 (i - 165888) (by omega)
  rwa [show 165888 + (i - 165888) = i by omega] at hk

theorem minUpTo_325 : ∀ i, i < 166912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 166400
  · exact minUpTo_324 i h
  have hk := mBlock325 (i - 166400) (by omega)
  rwa [show 166400 + (i - 166400) = i by omega] at hk

theorem minUpTo_326 : ∀ i, i < 167424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 166912
  · exact minUpTo_325 i h
  have hk := mBlock326 (i - 166912) (by omega)
  rwa [show 166912 + (i - 166912) = i by omega] at hk

theorem minUpTo_327 : ∀ i, i < 167936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 167424
  · exact minUpTo_326 i h
  have hk := mBlock327 (i - 167424) (by omega)
  rwa [show 167424 + (i - 167424) = i by omega] at hk

theorem minUpTo_328 : ∀ i, i < 168448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 167936
  · exact minUpTo_327 i h
  have hk := mBlock328 (i - 167936) (by omega)
  rwa [show 167936 + (i - 167936) = i by omega] at hk

theorem minUpTo_329 : ∀ i, i < 168960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 168448
  · exact minUpTo_328 i h
  have hk := mBlock329 (i - 168448) (by omega)
  rwa [show 168448 + (i - 168448) = i by omega] at hk

theorem minUpTo_330 : ∀ i, i < 169472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 168960
  · exact minUpTo_329 i h
  have hk := mBlock330 (i - 168960) (by omega)
  rwa [show 168960 + (i - 168960) = i by omega] at hk

theorem minUpTo_331 : ∀ i, i < 169984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 169472
  · exact minUpTo_330 i h
  have hk := mBlock331 (i - 169472) (by omega)
  rwa [show 169472 + (i - 169472) = i by omega] at hk

theorem minUpTo_332 : ∀ i, i < 170496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 169984
  · exact minUpTo_331 i h
  have hk := mBlock332 (i - 169984) (by omega)
  rwa [show 169984 + (i - 169984) = i by omega] at hk

theorem minUpTo_333 : ∀ i, i < 171008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 170496
  · exact minUpTo_332 i h
  have hk := mBlock333 (i - 170496) (by omega)
  rwa [show 170496 + (i - 170496) = i by omega] at hk

theorem minUpTo_334 : ∀ i, i < 171520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 171008
  · exact minUpTo_333 i h
  have hk := mBlock334 (i - 171008) (by omega)
  rwa [show 171008 + (i - 171008) = i by omega] at hk

theorem minUpTo_335 : ∀ i, i < 172032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 171520
  · exact minUpTo_334 i h
  have hk := mBlock335 (i - 171520) (by omega)
  rwa [show 171520 + (i - 171520) = i by omega] at hk

theorem minUpTo_336 : ∀ i, i < 172544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 172032
  · exact minUpTo_335 i h
  have hk := mBlock336 (i - 172032) (by omega)
  rwa [show 172032 + (i - 172032) = i by omega] at hk

theorem minUpTo_337 : ∀ i, i < 173056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 172544
  · exact minUpTo_336 i h
  have hk := mBlock337 (i - 172544) (by omega)
  rwa [show 172544 + (i - 172544) = i by omega] at hk

theorem minUpTo_338 : ∀ i, i < 173568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 173056
  · exact minUpTo_337 i h
  have hk := mBlock338 (i - 173056) (by omega)
  rwa [show 173056 + (i - 173056) = i by omega] at hk

theorem minUpTo_339 : ∀ i, i < 174080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 173568
  · exact minUpTo_338 i h
  have hk := mBlock339 (i - 173568) (by omega)
  rwa [show 173568 + (i - 173568) = i by omega] at hk

theorem minUpTo_340 : ∀ i, i < 174592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 174080
  · exact minUpTo_339 i h
  have hk := mBlock340 (i - 174080) (by omega)
  rwa [show 174080 + (i - 174080) = i by omega] at hk

theorem minUpTo_341 : ∀ i, i < 175104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 174592
  · exact minUpTo_340 i h
  have hk := mBlock341 (i - 174592) (by omega)
  rwa [show 174592 + (i - 174592) = i by omega] at hk

theorem minUpTo_342 : ∀ i, i < 175616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 175104
  · exact minUpTo_341 i h
  have hk := mBlock342 (i - 175104) (by omega)
  rwa [show 175104 + (i - 175104) = i by omega] at hk

theorem minUpTo_343 : ∀ i, i < 176128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 175616
  · exact minUpTo_342 i h
  have hk := mBlock343 (i - 175616) (by omega)
  rwa [show 175616 + (i - 175616) = i by omega] at hk

theorem minUpTo_344 : ∀ i, i < 176640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 176128
  · exact minUpTo_343 i h
  have hk := mBlock344 (i - 176128) (by omega)
  rwa [show 176128 + (i - 176128) = i by omega] at hk

theorem minUpTo_345 : ∀ i, i < 177152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 176640
  · exact minUpTo_344 i h
  have hk := mBlock345 (i - 176640) (by omega)
  rwa [show 176640 + (i - 176640) = i by omega] at hk

theorem minUpTo_346 : ∀ i, i < 177664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 177152
  · exact minUpTo_345 i h
  have hk := mBlock346 (i - 177152) (by omega)
  rwa [show 177152 + (i - 177152) = i by omega] at hk

theorem minUpTo_347 : ∀ i, i < 178176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 177664
  · exact minUpTo_346 i h
  have hk := mBlock347 (i - 177664) (by omega)
  rwa [show 177664 + (i - 177664) = i by omega] at hk

theorem minUpTo_348 : ∀ i, i < 178688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 178176
  · exact minUpTo_347 i h
  have hk := mBlock348 (i - 178176) (by omega)
  rwa [show 178176 + (i - 178176) = i by omega] at hk

theorem minUpTo_349 : ∀ i, i < 179200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 178688
  · exact minUpTo_348 i h
  have hk := mBlock349 (i - 178688) (by omega)
  rwa [show 178688 + (i - 178688) = i by omega] at hk

theorem minUpTo_350 : ∀ i, i < 179712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 179200
  · exact minUpTo_349 i h
  have hk := mBlock350 (i - 179200) (by omega)
  rwa [show 179200 + (i - 179200) = i by omega] at hk

theorem minUpTo_351 : ∀ i, i < 180224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 179712
  · exact minUpTo_350 i h
  have hk := mBlock351 (i - 179712) (by omega)
  rwa [show 179712 + (i - 179712) = i by omega] at hk

theorem minUpTo_352 : ∀ i, i < 180736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 180224
  · exact minUpTo_351 i h
  have hk := mBlock352 (i - 180224) (by omega)
  rwa [show 180224 + (i - 180224) = i by omega] at hk

theorem minUpTo_353 : ∀ i, i < 181248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 180736
  · exact minUpTo_352 i h
  have hk := mBlock353 (i - 180736) (by omega)
  rwa [show 180736 + (i - 180736) = i by omega] at hk

theorem minUpTo_354 : ∀ i, i < 181760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 181248
  · exact minUpTo_353 i h
  have hk := mBlock354 (i - 181248) (by omega)
  rwa [show 181248 + (i - 181248) = i by omega] at hk

theorem minUpTo_355 : ∀ i, i < 182272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 181760
  · exact minUpTo_354 i h
  have hk := mBlock355 (i - 181760) (by omega)
  rwa [show 181760 + (i - 181760) = i by omega] at hk

theorem minUpTo_356 : ∀ i, i < 182784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 182272
  · exact minUpTo_355 i h
  have hk := mBlock356 (i - 182272) (by omega)
  rwa [show 182272 + (i - 182272) = i by omega] at hk

theorem minUpTo_357 : ∀ i, i < 183296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 182784
  · exact minUpTo_356 i h
  have hk := mBlock357 (i - 182784) (by omega)
  rwa [show 182784 + (i - 182784) = i by omega] at hk

theorem minUpTo_358 : ∀ i, i < 183808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 183296
  · exact minUpTo_357 i h
  have hk := mBlock358 (i - 183296) (by omega)
  rwa [show 183296 + (i - 183296) = i by omega] at hk

theorem minUpTo_359 : ∀ i, i < 184320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 183808
  · exact minUpTo_358 i h
  have hk := mBlock359 (i - 183808) (by omega)
  rwa [show 183808 + (i - 183808) = i by omega] at hk

theorem minUpTo_360 : ∀ i, i < 184832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 184320
  · exact minUpTo_359 i h
  have hk := mBlock360 (i - 184320) (by omega)
  rwa [show 184320 + (i - 184320) = i by omega] at hk

theorem minUpTo_361 : ∀ i, i < 185344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 184832
  · exact minUpTo_360 i h
  have hk := mBlock361 (i - 184832) (by omega)
  rwa [show 184832 + (i - 184832) = i by omega] at hk

theorem minUpTo_362 : ∀ i, i < 185856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 185344
  · exact minUpTo_361 i h
  have hk := mBlock362 (i - 185344) (by omega)
  rwa [show 185344 + (i - 185344) = i by omega] at hk

theorem minUpTo_363 : ∀ i, i < 186368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 185856
  · exact minUpTo_362 i h
  have hk := mBlock363 (i - 185856) (by omega)
  rwa [show 185856 + (i - 185856) = i by omega] at hk

theorem minUpTo_364 : ∀ i, i < 186880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 186368
  · exact minUpTo_363 i h
  have hk := mBlock364 (i - 186368) (by omega)
  rwa [show 186368 + (i - 186368) = i by omega] at hk

theorem minUpTo_365 : ∀ i, i < 187392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 186880
  · exact minUpTo_364 i h
  have hk := mBlock365 (i - 186880) (by omega)
  rwa [show 186880 + (i - 186880) = i by omega] at hk

theorem minUpTo_366 : ∀ i, i < 187904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 187392
  · exact minUpTo_365 i h
  have hk := mBlock366 (i - 187392) (by omega)
  rwa [show 187392 + (i - 187392) = i by omega] at hk

theorem minUpTo_367 : ∀ i, i < 188416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 187904
  · exact minUpTo_366 i h
  have hk := mBlock367 (i - 187904) (by omega)
  rwa [show 187904 + (i - 187904) = i by omega] at hk

theorem minUpTo_368 : ∀ i, i < 188928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 188416
  · exact minUpTo_367 i h
  have hk := mBlock368 (i - 188416) (by omega)
  rwa [show 188416 + (i - 188416) = i by omega] at hk

theorem minUpTo_369 : ∀ i, i < 189440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 188928
  · exact minUpTo_368 i h
  have hk := mBlock369 (i - 188928) (by omega)
  rwa [show 188928 + (i - 188928) = i by omega] at hk

theorem minUpTo_370 : ∀ i, i < 189952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 189440
  · exact minUpTo_369 i h
  have hk := mBlock370 (i - 189440) (by omega)
  rwa [show 189440 + (i - 189440) = i by omega] at hk

theorem minUpTo_371 : ∀ i, i < 190464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 189952
  · exact minUpTo_370 i h
  have hk := mBlock371 (i - 189952) (by omega)
  rwa [show 189952 + (i - 189952) = i by omega] at hk

theorem minUpTo_372 : ∀ i, i < 190976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 190464
  · exact minUpTo_371 i h
  have hk := mBlock372 (i - 190464) (by omega)
  rwa [show 190464 + (i - 190464) = i by omega] at hk

theorem minUpTo_373 : ∀ i, i < 191488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 190976
  · exact minUpTo_372 i h
  have hk := mBlock373 (i - 190976) (by omega)
  rwa [show 190976 + (i - 190976) = i by omega] at hk

theorem minUpTo_374 : ∀ i, i < 192000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 191488
  · exact minUpTo_373 i h
  have hk := mBlock374 (i - 191488) (by omega)
  rwa [show 191488 + (i - 191488) = i by omega] at hk

theorem minUpTo_375 : ∀ i, i < 192512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 192000
  · exact minUpTo_374 i h
  have hk := mBlock375 (i - 192000) (by omega)
  rwa [show 192000 + (i - 192000) = i by omega] at hk

theorem minUpTo_376 : ∀ i, i < 193024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 192512
  · exact minUpTo_375 i h
  have hk := mBlock376 (i - 192512) (by omega)
  rwa [show 192512 + (i - 192512) = i by omega] at hk

theorem minUpTo_377 : ∀ i, i < 193536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 193024
  · exact minUpTo_376 i h
  have hk := mBlock377 (i - 193024) (by omega)
  rwa [show 193024 + (i - 193024) = i by omega] at hk

theorem minUpTo_378 : ∀ i, i < 194048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 193536
  · exact minUpTo_377 i h
  have hk := mBlock378 (i - 193536) (by omega)
  rwa [show 193536 + (i - 193536) = i by omega] at hk

theorem minUpTo_379 : ∀ i, i < 194560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 194048
  · exact minUpTo_378 i h
  have hk := mBlock379 (i - 194048) (by omega)
  rwa [show 194048 + (i - 194048) = i by omega] at hk

theorem minUpTo_380 : ∀ i, i < 195072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 194560
  · exact minUpTo_379 i h
  have hk := mBlock380 (i - 194560) (by omega)
  rwa [show 194560 + (i - 194560) = i by omega] at hk

theorem minUpTo_381 : ∀ i, i < 195584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 195072
  · exact minUpTo_380 i h
  have hk := mBlock381 (i - 195072) (by omega)
  rwa [show 195072 + (i - 195072) = i by omega] at hk

theorem minUpTo_382 : ∀ i, i < 196096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 195584
  · exact minUpTo_381 i h
  have hk := mBlock382 (i - 195584) (by omega)
  rwa [show 195584 + (i - 195584) = i by omega] at hk

theorem minUpTo_383 : ∀ i, i < 196608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 196096
  · exact minUpTo_382 i h
  have hk := mBlock383 (i - 196096) (by omega)
  rwa [show 196096 + (i - 196096) = i by omega] at hk

theorem minUpTo_384 : ∀ i, i < 197120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 196608
  · exact minUpTo_383 i h
  have hk := mBlock384 (i - 196608) (by omega)
  rwa [show 196608 + (i - 196608) = i by omega] at hk

theorem minUpTo_385 : ∀ i, i < 197632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 197120
  · exact minUpTo_384 i h
  have hk := mBlock385 (i - 197120) (by omega)
  rwa [show 197120 + (i - 197120) = i by omega] at hk

theorem minUpTo_386 : ∀ i, i < 198144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 197632
  · exact minUpTo_385 i h
  have hk := mBlock386 (i - 197632) (by omega)
  rwa [show 197632 + (i - 197632) = i by omega] at hk

theorem minUpTo_387 : ∀ i, i < 198656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 198144
  · exact minUpTo_386 i h
  have hk := mBlock387 (i - 198144) (by omega)
  rwa [show 198144 + (i - 198144) = i by omega] at hk

theorem minUpTo_388 : ∀ i, i < 199168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 198656
  · exact minUpTo_387 i h
  have hk := mBlock388 (i - 198656) (by omega)
  rwa [show 198656 + (i - 198656) = i by omega] at hk

theorem minUpTo_389 : ∀ i, i < 199680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 199168
  · exact minUpTo_388 i h
  have hk := mBlock389 (i - 199168) (by omega)
  rwa [show 199168 + (i - 199168) = i by omega] at hk

theorem minUpTo_390 : ∀ i, i < 200192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 199680
  · exact minUpTo_389 i h
  have hk := mBlock390 (i - 199680) (by omega)
  rwa [show 199680 + (i - 199680) = i by omega] at hk

theorem minUpTo_391 : ∀ i, i < 200704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 200192
  · exact minUpTo_390 i h
  have hk := mBlock391 (i - 200192) (by omega)
  rwa [show 200192 + (i - 200192) = i by omega] at hk

theorem minUpTo_392 : ∀ i, i < 201216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 200704
  · exact minUpTo_391 i h
  have hk := mBlock392 (i - 200704) (by omega)
  rwa [show 200704 + (i - 200704) = i by omega] at hk

theorem minUpTo_393 : ∀ i, i < 201728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 201216
  · exact minUpTo_392 i h
  have hk := mBlock393 (i - 201216) (by omega)
  rwa [show 201216 + (i - 201216) = i by omega] at hk

theorem minUpTo_394 : ∀ i, i < 202240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 201728
  · exact minUpTo_393 i h
  have hk := mBlock394 (i - 201728) (by omega)
  rwa [show 201728 + (i - 201728) = i by omega] at hk

theorem minUpTo_395 : ∀ i, i < 202752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 202240
  · exact minUpTo_394 i h
  have hk := mBlock395 (i - 202240) (by omega)
  rwa [show 202240 + (i - 202240) = i by omega] at hk

theorem minUpTo_396 : ∀ i, i < 203264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 202752
  · exact minUpTo_395 i h
  have hk := mBlock396 (i - 202752) (by omega)
  rwa [show 202752 + (i - 202752) = i by omega] at hk

theorem minUpTo_397 : ∀ i, i < 203776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 203264
  · exact minUpTo_396 i h
  have hk := mBlock397 (i - 203264) (by omega)
  rwa [show 203264 + (i - 203264) = i by omega] at hk

theorem minUpTo_398 : ∀ i, i < 204288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 203776
  · exact minUpTo_397 i h
  have hk := mBlock398 (i - 203776) (by omega)
  rwa [show 203776 + (i - 203776) = i by omega] at hk

theorem minUpTo_399 : ∀ i, i < 204800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 204288
  · exact minUpTo_398 i h
  have hk := mBlock399 (i - 204288) (by omega)
  rwa [show 204288 + (i - 204288) = i by omega] at hk

theorem minUpTo_400 : ∀ i, i < 205312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 204800
  · exact minUpTo_399 i h
  have hk := mBlock400 (i - 204800) (by omega)
  rwa [show 204800 + (i - 204800) = i by omega] at hk

theorem minUpTo_401 : ∀ i, i < 205824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 205312
  · exact minUpTo_400 i h
  have hk := mBlock401 (i - 205312) (by omega)
  rwa [show 205312 + (i - 205312) = i by omega] at hk

theorem minUpTo_402 : ∀ i, i < 206336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 205824
  · exact minUpTo_401 i h
  have hk := mBlock402 (i - 205824) (by omega)
  rwa [show 205824 + (i - 205824) = i by omega] at hk

theorem minUpTo_403 : ∀ i, i < 206848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 206336
  · exact minUpTo_402 i h
  have hk := mBlock403 (i - 206336) (by omega)
  rwa [show 206336 + (i - 206336) = i by omega] at hk

theorem minUpTo_404 : ∀ i, i < 207360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 206848
  · exact minUpTo_403 i h
  have hk := mBlock404 (i - 206848) (by omega)
  rwa [show 206848 + (i - 206848) = i by omega] at hk

theorem minUpTo_405 : ∀ i, i < 207872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 207360
  · exact minUpTo_404 i h
  have hk := mBlock405 (i - 207360) (by omega)
  rwa [show 207360 + (i - 207360) = i by omega] at hk

theorem minUpTo_406 : ∀ i, i < 208384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 207872
  · exact minUpTo_405 i h
  have hk := mBlock406 (i - 207872) (by omega)
  rwa [show 207872 + (i - 207872) = i by omega] at hk

theorem minUpTo_407 : ∀ i, i < 208896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 208384
  · exact minUpTo_406 i h
  have hk := mBlock407 (i - 208384) (by omega)
  rwa [show 208384 + (i - 208384) = i by omega] at hk

theorem minUpTo_408 : ∀ i, i < 209408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 208896
  · exact minUpTo_407 i h
  have hk := mBlock408 (i - 208896) (by omega)
  rwa [show 208896 + (i - 208896) = i by omega] at hk

theorem minUpTo_409 : ∀ i, i < 209920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 209408
  · exact minUpTo_408 i h
  have hk := mBlock409 (i - 209408) (by omega)
  rwa [show 209408 + (i - 209408) = i by omega] at hk

theorem minUpTo_410 : ∀ i, i < 210432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 209920
  · exact minUpTo_409 i h
  have hk := mBlock410 (i - 209920) (by omega)
  rwa [show 209920 + (i - 209920) = i by omega] at hk

theorem minUpTo_411 : ∀ i, i < 210944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 210432
  · exact minUpTo_410 i h
  have hk := mBlock411 (i - 210432) (by omega)
  rwa [show 210432 + (i - 210432) = i by omega] at hk

theorem minUpTo_412 : ∀ i, i < 211456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 210944
  · exact minUpTo_411 i h
  have hk := mBlock412 (i - 210944) (by omega)
  rwa [show 210944 + (i - 210944) = i by omega] at hk

theorem minUpTo_413 : ∀ i, i < 211968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 211456
  · exact minUpTo_412 i h
  have hk := mBlock413 (i - 211456) (by omega)
  rwa [show 211456 + (i - 211456) = i by omega] at hk

theorem minUpTo_414 : ∀ i, i < 212480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 211968
  · exact minUpTo_413 i h
  have hk := mBlock414 (i - 211968) (by omega)
  rwa [show 211968 + (i - 211968) = i by omega] at hk

theorem minUpTo_415 : ∀ i, i < 212992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 212480
  · exact minUpTo_414 i h
  have hk := mBlock415 (i - 212480) (by omega)
  rwa [show 212480 + (i - 212480) = i by omega] at hk

theorem minUpTo_416 : ∀ i, i < 213504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 212992
  · exact minUpTo_415 i h
  have hk := mBlock416 (i - 212992) (by omega)
  rwa [show 212992 + (i - 212992) = i by omega] at hk

theorem minUpTo_417 : ∀ i, i < 214016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 213504
  · exact minUpTo_416 i h
  have hk := mBlock417 (i - 213504) (by omega)
  rwa [show 213504 + (i - 213504) = i by omega] at hk

theorem minUpTo_418 : ∀ i, i < 214528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 214016
  · exact minUpTo_417 i h
  have hk := mBlock418 (i - 214016) (by omega)
  rwa [show 214016 + (i - 214016) = i by omega] at hk

theorem minUpTo_419 : ∀ i, i < 215040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 214528
  · exact minUpTo_418 i h
  have hk := mBlock419 (i - 214528) (by omega)
  rwa [show 214528 + (i - 214528) = i by omega] at hk

theorem minUpTo_420 : ∀ i, i < 215552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 215040
  · exact minUpTo_419 i h
  have hk := mBlock420 (i - 215040) (by omega)
  rwa [show 215040 + (i - 215040) = i by omega] at hk

theorem minUpTo_421 : ∀ i, i < 216064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 215552
  · exact minUpTo_420 i h
  have hk := mBlock421 (i - 215552) (by omega)
  rwa [show 215552 + (i - 215552) = i by omega] at hk

theorem minUpTo_422 : ∀ i, i < 216576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 216064
  · exact minUpTo_421 i h
  have hk := mBlock422 (i - 216064) (by omega)
  rwa [show 216064 + (i - 216064) = i by omega] at hk

theorem minUpTo_423 : ∀ i, i < 217088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 216576
  · exact minUpTo_422 i h
  have hk := mBlock423 (i - 216576) (by omega)
  rwa [show 216576 + (i - 216576) = i by omega] at hk

theorem minUpTo_424 : ∀ i, i < 217600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 217088
  · exact minUpTo_423 i h
  have hk := mBlock424 (i - 217088) (by omega)
  rwa [show 217088 + (i - 217088) = i by omega] at hk

theorem minUpTo_425 : ∀ i, i < 218112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 217600
  · exact minUpTo_424 i h
  have hk := mBlock425 (i - 217600) (by omega)
  rwa [show 217600 + (i - 217600) = i by omega] at hk

theorem minUpTo_426 : ∀ i, i < 218624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 218112
  · exact minUpTo_425 i h
  have hk := mBlock426 (i - 218112) (by omega)
  rwa [show 218112 + (i - 218112) = i by omega] at hk

theorem minUpTo_427 : ∀ i, i < 219136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 218624
  · exact minUpTo_426 i h
  have hk := mBlock427 (i - 218624) (by omega)
  rwa [show 218624 + (i - 218624) = i by omega] at hk

theorem minUpTo_428 : ∀ i, i < 219648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 219136
  · exact minUpTo_427 i h
  have hk := mBlock428 (i - 219136) (by omega)
  rwa [show 219136 + (i - 219136) = i by omega] at hk

theorem minUpTo_429 : ∀ i, i < 220160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 219648
  · exact minUpTo_428 i h
  have hk := mBlock429 (i - 219648) (by omega)
  rwa [show 219648 + (i - 219648) = i by omega] at hk

theorem minUpTo_430 : ∀ i, i < 220672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 220160
  · exact minUpTo_429 i h
  have hk := mBlock430 (i - 220160) (by omega)
  rwa [show 220160 + (i - 220160) = i by omega] at hk

theorem minUpTo_431 : ∀ i, i < 221184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 220672
  · exact minUpTo_430 i h
  have hk := mBlock431 (i - 220672) (by omega)
  rwa [show 220672 + (i - 220672) = i by omega] at hk

theorem minUpTo_432 : ∀ i, i < 221696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 221184
  · exact minUpTo_431 i h
  have hk := mBlock432 (i - 221184) (by omega)
  rwa [show 221184 + (i - 221184) = i by omega] at hk

theorem minUpTo_433 : ∀ i, i < 222208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 221696
  · exact minUpTo_432 i h
  have hk := mBlock433 (i - 221696) (by omega)
  rwa [show 221696 + (i - 221696) = i by omega] at hk

theorem minUpTo_434 : ∀ i, i < 222720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 222208
  · exact minUpTo_433 i h
  have hk := mBlock434 (i - 222208) (by omega)
  rwa [show 222208 + (i - 222208) = i by omega] at hk

theorem minUpTo_435 : ∀ i, i < 223232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 222720
  · exact minUpTo_434 i h
  have hk := mBlock435 (i - 222720) (by omega)
  rwa [show 222720 + (i - 222720) = i by omega] at hk

theorem minUpTo_436 : ∀ i, i < 223744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 223232
  · exact minUpTo_435 i h
  have hk := mBlock436 (i - 223232) (by omega)
  rwa [show 223232 + (i - 223232) = i by omega] at hk

theorem minUpTo_437 : ∀ i, i < 224256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 223744
  · exact minUpTo_436 i h
  have hk := mBlock437 (i - 223744) (by omega)
  rwa [show 223744 + (i - 223744) = i by omega] at hk

theorem minUpTo_438 : ∀ i, i < 224768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 224256
  · exact minUpTo_437 i h
  have hk := mBlock438 (i - 224256) (by omega)
  rwa [show 224256 + (i - 224256) = i by omega] at hk

theorem minUpTo_439 : ∀ i, i < 225280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 224768
  · exact minUpTo_438 i h
  have hk := mBlock439 (i - 224768) (by omega)
  rwa [show 224768 + (i - 224768) = i by omega] at hk

theorem minUpTo_440 : ∀ i, i < 225792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 225280
  · exact minUpTo_439 i h
  have hk := mBlock440 (i - 225280) (by omega)
  rwa [show 225280 + (i - 225280) = i by omega] at hk

theorem minUpTo_441 : ∀ i, i < 226304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 225792
  · exact minUpTo_440 i h
  have hk := mBlock441 (i - 225792) (by omega)
  rwa [show 225792 + (i - 225792) = i by omega] at hk

theorem minUpTo_442 : ∀ i, i < 226816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 226304
  · exact minUpTo_441 i h
  have hk := mBlock442 (i - 226304) (by omega)
  rwa [show 226304 + (i - 226304) = i by omega] at hk

theorem minUpTo_443 : ∀ i, i < 227328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 226816
  · exact minUpTo_442 i h
  have hk := mBlock443 (i - 226816) (by omega)
  rwa [show 226816 + (i - 226816) = i by omega] at hk

theorem minUpTo_444 : ∀ i, i < 227840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 227328
  · exact minUpTo_443 i h
  have hk := mBlock444 (i - 227328) (by omega)
  rwa [show 227328 + (i - 227328) = i by omega] at hk

theorem minUpTo_445 : ∀ i, i < 228352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 227840
  · exact minUpTo_444 i h
  have hk := mBlock445 (i - 227840) (by omega)
  rwa [show 227840 + (i - 227840) = i by omega] at hk

theorem minUpTo_446 : ∀ i, i < 228864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 228352
  · exact minUpTo_445 i h
  have hk := mBlock446 (i - 228352) (by omega)
  rwa [show 228352 + (i - 228352) = i by omega] at hk

theorem minUpTo_447 : ∀ i, i < 229376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 228864
  · exact minUpTo_446 i h
  have hk := mBlock447 (i - 228864) (by omega)
  rwa [show 228864 + (i - 228864) = i by omega] at hk

theorem minUpTo_448 : ∀ i, i < 229888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 229376
  · exact minUpTo_447 i h
  have hk := mBlock448 (i - 229376) (by omega)
  rwa [show 229376 + (i - 229376) = i by omega] at hk

theorem minUpTo_449 : ∀ i, i < 230400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 229888
  · exact minUpTo_448 i h
  have hk := mBlock449 (i - 229888) (by omega)
  rwa [show 229888 + (i - 229888) = i by omega] at hk

theorem minUpTo_450 : ∀ i, i < 230912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 230400
  · exact minUpTo_449 i h
  have hk := mBlock450 (i - 230400) (by omega)
  rwa [show 230400 + (i - 230400) = i by omega] at hk

theorem minUpTo_451 : ∀ i, i < 231424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 230912
  · exact minUpTo_450 i h
  have hk := mBlock451 (i - 230912) (by omega)
  rwa [show 230912 + (i - 230912) = i by omega] at hk

theorem minUpTo_452 : ∀ i, i < 231936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 231424
  · exact minUpTo_451 i h
  have hk := mBlock452 (i - 231424) (by omega)
  rwa [show 231424 + (i - 231424) = i by omega] at hk

theorem minUpTo_453 : ∀ i, i < 232448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 231936
  · exact minUpTo_452 i h
  have hk := mBlock453 (i - 231936) (by omega)
  rwa [show 231936 + (i - 231936) = i by omega] at hk

theorem minUpTo_454 : ∀ i, i < 232960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 232448
  · exact minUpTo_453 i h
  have hk := mBlock454 (i - 232448) (by omega)
  rwa [show 232448 + (i - 232448) = i by omega] at hk

theorem minUpTo_455 : ∀ i, i < 233472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 232960
  · exact minUpTo_454 i h
  have hk := mBlock455 (i - 232960) (by omega)
  rwa [show 232960 + (i - 232960) = i by omega] at hk

theorem minUpTo_456 : ∀ i, i < 233984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 233472
  · exact minUpTo_455 i h
  have hk := mBlock456 (i - 233472) (by omega)
  rwa [show 233472 + (i - 233472) = i by omega] at hk

theorem minUpTo_457 : ∀ i, i < 234496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 233984
  · exact minUpTo_456 i h
  have hk := mBlock457 (i - 233984) (by omega)
  rwa [show 233984 + (i - 233984) = i by omega] at hk

theorem minUpTo_458 : ∀ i, i < 235008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 234496
  · exact minUpTo_457 i h
  have hk := mBlock458 (i - 234496) (by omega)
  rwa [show 234496 + (i - 234496) = i by omega] at hk

theorem minUpTo_459 : ∀ i, i < 235520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 235008
  · exact minUpTo_458 i h
  have hk := mBlock459 (i - 235008) (by omega)
  rwa [show 235008 + (i - 235008) = i by omega] at hk

theorem minUpTo_460 : ∀ i, i < 236032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 235520
  · exact minUpTo_459 i h
  have hk := mBlock460 (i - 235520) (by omega)
  rwa [show 235520 + (i - 235520) = i by omega] at hk

theorem minUpTo_461 : ∀ i, i < 236544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 236032
  · exact minUpTo_460 i h
  have hk := mBlock461 (i - 236032) (by omega)
  rwa [show 236032 + (i - 236032) = i by omega] at hk

theorem minUpTo_462 : ∀ i, i < 237056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 236544
  · exact minUpTo_461 i h
  have hk := mBlock462 (i - 236544) (by omega)
  rwa [show 236544 + (i - 236544) = i by omega] at hk

theorem minUpTo_463 : ∀ i, i < 237568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 237056
  · exact minUpTo_462 i h
  have hk := mBlock463 (i - 237056) (by omega)
  rwa [show 237056 + (i - 237056) = i by omega] at hk

theorem minUpTo_464 : ∀ i, i < 238080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 237568
  · exact minUpTo_463 i h
  have hk := mBlock464 (i - 237568) (by omega)
  rwa [show 237568 + (i - 237568) = i by omega] at hk

theorem minUpTo_465 : ∀ i, i < 238592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 238080
  · exact minUpTo_464 i h
  have hk := mBlock465 (i - 238080) (by omega)
  rwa [show 238080 + (i - 238080) = i by omega] at hk

theorem minUpTo_466 : ∀ i, i < 239104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 238592
  · exact minUpTo_465 i h
  have hk := mBlock466 (i - 238592) (by omega)
  rwa [show 238592 + (i - 238592) = i by omega] at hk

theorem minUpTo_467 : ∀ i, i < 239616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 239104
  · exact minUpTo_466 i h
  have hk := mBlock467 (i - 239104) (by omega)
  rwa [show 239104 + (i - 239104) = i by omega] at hk

theorem minUpTo_468 : ∀ i, i < 240128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 239616
  · exact minUpTo_467 i h
  have hk := mBlock468 (i - 239616) (by omega)
  rwa [show 239616 + (i - 239616) = i by omega] at hk

theorem minUpTo_469 : ∀ i, i < 240640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 240128
  · exact minUpTo_468 i h
  have hk := mBlock469 (i - 240128) (by omega)
  rwa [show 240128 + (i - 240128) = i by omega] at hk

theorem minUpTo_470 : ∀ i, i < 241152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 240640
  · exact minUpTo_469 i h
  have hk := mBlock470 (i - 240640) (by omega)
  rwa [show 240640 + (i - 240640) = i by omega] at hk

theorem minUpTo_471 : ∀ i, i < 241664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 241152
  · exact minUpTo_470 i h
  have hk := mBlock471 (i - 241152) (by omega)
  rwa [show 241152 + (i - 241152) = i by omega] at hk

theorem minUpTo_472 : ∀ i, i < 242176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 241664
  · exact minUpTo_471 i h
  have hk := mBlock472 (i - 241664) (by omega)
  rwa [show 241664 + (i - 241664) = i by omega] at hk

theorem minUpTo_473 : ∀ i, i < 242688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 242176
  · exact minUpTo_472 i h
  have hk := mBlock473 (i - 242176) (by omega)
  rwa [show 242176 + (i - 242176) = i by omega] at hk

theorem minUpTo_474 : ∀ i, i < 243200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 242688
  · exact minUpTo_473 i h
  have hk := mBlock474 (i - 242688) (by omega)
  rwa [show 242688 + (i - 242688) = i by omega] at hk

theorem minUpTo_475 : ∀ i, i < 243712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 243200
  · exact minUpTo_474 i h
  have hk := mBlock475 (i - 243200) (by omega)
  rwa [show 243200 + (i - 243200) = i by omega] at hk

theorem minUpTo_476 : ∀ i, i < 244224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 243712
  · exact minUpTo_475 i h
  have hk := mBlock476 (i - 243712) (by omega)
  rwa [show 243712 + (i - 243712) = i by omega] at hk

theorem minUpTo_477 : ∀ i, i < 244736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 244224
  · exact minUpTo_476 i h
  have hk := mBlock477 (i - 244224) (by omega)
  rwa [show 244224 + (i - 244224) = i by omega] at hk

theorem minUpTo_478 : ∀ i, i < 245248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 244736
  · exact minUpTo_477 i h
  have hk := mBlock478 (i - 244736) (by omega)
  rwa [show 244736 + (i - 244736) = i by omega] at hk

theorem minUpTo_479 : ∀ i, i < 245760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 245248
  · exact minUpTo_478 i h
  have hk := mBlock479 (i - 245248) (by omega)
  rwa [show 245248 + (i - 245248) = i by omega] at hk

theorem minUpTo_480 : ∀ i, i < 246272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 245760
  · exact minUpTo_479 i h
  have hk := mBlock480 (i - 245760) (by omega)
  rwa [show 245760 + (i - 245760) = i by omega] at hk

theorem minUpTo_481 : ∀ i, i < 246784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 246272
  · exact minUpTo_480 i h
  have hk := mBlock481 (i - 246272) (by omega)
  rwa [show 246272 + (i - 246272) = i by omega] at hk

theorem minUpTo_482 : ∀ i, i < 247296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 246784
  · exact minUpTo_481 i h
  have hk := mBlock482 (i - 246784) (by omega)
  rwa [show 246784 + (i - 246784) = i by omega] at hk

theorem minUpTo_483 : ∀ i, i < 247808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 247296
  · exact minUpTo_482 i h
  have hk := mBlock483 (i - 247296) (by omega)
  rwa [show 247296 + (i - 247296) = i by omega] at hk

theorem minUpTo_484 : ∀ i, i < 248320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 247808
  · exact minUpTo_483 i h
  have hk := mBlock484 (i - 247808) (by omega)
  rwa [show 247808 + (i - 247808) = i by omega] at hk

theorem minUpTo_485 : ∀ i, i < 248832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 248320
  · exact minUpTo_484 i h
  have hk := mBlock485 (i - 248320) (by omega)
  rwa [show 248320 + (i - 248320) = i by omega] at hk

theorem minUpTo_486 : ∀ i, i < 249344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 248832
  · exact minUpTo_485 i h
  have hk := mBlock486 (i - 248832) (by omega)
  rwa [show 248832 + (i - 248832) = i by omega] at hk

theorem minUpTo_487 : ∀ i, i < 249856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 249344
  · exact minUpTo_486 i h
  have hk := mBlock487 (i - 249344) (by omega)
  rwa [show 249344 + (i - 249344) = i by omega] at hk

theorem minUpTo_488 : ∀ i, i < 250368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 249856
  · exact minUpTo_487 i h
  have hk := mBlock488 (i - 249856) (by omega)
  rwa [show 249856 + (i - 249856) = i by omega] at hk

theorem minUpTo_489 : ∀ i, i < 250880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 250368
  · exact minUpTo_488 i h
  have hk := mBlock489 (i - 250368) (by omega)
  rwa [show 250368 + (i - 250368) = i by omega] at hk

theorem minUpTo_490 : ∀ i, i < 251392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 250880
  · exact minUpTo_489 i h
  have hk := mBlock490 (i - 250880) (by omega)
  rwa [show 250880 + (i - 250880) = i by omega] at hk

theorem minUpTo_491 : ∀ i, i < 251904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 251392
  · exact minUpTo_490 i h
  have hk := mBlock491 (i - 251392) (by omega)
  rwa [show 251392 + (i - 251392) = i by omega] at hk

theorem minUpTo_492 : ∀ i, i < 252416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 251904
  · exact minUpTo_491 i h
  have hk := mBlock492 (i - 251904) (by omega)
  rwa [show 251904 + (i - 251904) = i by omega] at hk

theorem minUpTo_493 : ∀ i, i < 252928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 252416
  · exact minUpTo_492 i h
  have hk := mBlock493 (i - 252416) (by omega)
  rwa [show 252416 + (i - 252416) = i by omega] at hk

theorem minUpTo_494 : ∀ i, i < 253440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 252928
  · exact minUpTo_493 i h
  have hk := mBlock494 (i - 252928) (by omega)
  rwa [show 252928 + (i - 252928) = i by omega] at hk

theorem minUpTo_495 : ∀ i, i < 253952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 253440
  · exact minUpTo_494 i h
  have hk := mBlock495 (i - 253440) (by omega)
  rwa [show 253440 + (i - 253440) = i by omega] at hk

theorem minUpTo_496 : ∀ i, i < 254464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 253952
  · exact minUpTo_495 i h
  have hk := mBlock496 (i - 253952) (by omega)
  rwa [show 253952 + (i - 253952) = i by omega] at hk

theorem minUpTo_497 : ∀ i, i < 254976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 254464
  · exact minUpTo_496 i h
  have hk := mBlock497 (i - 254464) (by omega)
  rwa [show 254464 + (i - 254464) = i by omega] at hk

theorem minUpTo_498 : ∀ i, i < 255488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 254976
  · exact minUpTo_497 i h
  have hk := mBlock498 (i - 254976) (by omega)
  rwa [show 254976 + (i - 254976) = i by omega] at hk

theorem minUpTo_499 : ∀ i, i < 256000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 255488
  · exact minUpTo_498 i h
  have hk := mBlock499 (i - 255488) (by omega)
  rwa [show 255488 + (i - 255488) = i by omega] at hk

theorem minUpTo_500 : ∀ i, i < 256512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 256000
  · exact minUpTo_499 i h
  have hk := mBlock500 (i - 256000) (by omega)
  rwa [show 256000 + (i - 256000) = i by omega] at hk

theorem minUpTo_501 : ∀ i, i < 257024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 256512
  · exact minUpTo_500 i h
  have hk := mBlock501 (i - 256512) (by omega)
  rwa [show 256512 + (i - 256512) = i by omega] at hk

theorem minUpTo_502 : ∀ i, i < 257536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 257024
  · exact minUpTo_501 i h
  have hk := mBlock502 (i - 257024) (by omega)
  rwa [show 257024 + (i - 257024) = i by omega] at hk

theorem minUpTo_503 : ∀ i, i < 258048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 257536
  · exact minUpTo_502 i h
  have hk := mBlock503 (i - 257536) (by omega)
  rwa [show 257536 + (i - 257536) = i by omega] at hk

theorem minUpTo_504 : ∀ i, i < 258560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 258048
  · exact minUpTo_503 i h
  have hk := mBlock504 (i - 258048) (by omega)
  rwa [show 258048 + (i - 258048) = i by omega] at hk

theorem minUpTo_505 : ∀ i, i < 259072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 258560
  · exact minUpTo_504 i h
  have hk := mBlock505 (i - 258560) (by omega)
  rwa [show 258560 + (i - 258560) = i by omega] at hk

theorem minUpTo_506 : ∀ i, i < 259584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 259072
  · exact minUpTo_505 i h
  have hk := mBlock506 (i - 259072) (by omega)
  rwa [show 259072 + (i - 259072) = i by omega] at hk

theorem minUpTo_507 : ∀ i, i < 260096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 259584
  · exact minUpTo_506 i h
  have hk := mBlock507 (i - 259584) (by omega)
  rwa [show 259584 + (i - 259584) = i by omega] at hk

theorem minUpTo_508 : ∀ i, i < 260608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 260096
  · exact minUpTo_507 i h
  have hk := mBlock508 (i - 260096) (by omega)
  rwa [show 260096 + (i - 260096) = i by omega] at hk

theorem minUpTo_509 : ∀ i, i < 261120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 260608
  · exact minUpTo_508 i h
  have hk := mBlock509 (i - 260608) (by omega)
  rwa [show 260608 + (i - 260608) = i by omega] at hk

theorem minUpTo_510 : ∀ i, i < 261632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 261120
  · exact minUpTo_509 i h
  have hk := mBlock510 (i - 261120) (by omega)
  rwa [show 261120 + (i - 261120) = i by omega] at hk

theorem minUpTo_511 : ∀ i, i < 262144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 261632
  · exact minUpTo_510 i h
  have hk := mBlock511 (i - 261632) (by omega)
  rwa [show 261632 + (i - 261632) = i by omega] at hk

theorem minUpTo_512 : ∀ i, i < 262656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 262144
  · exact minUpTo_511 i h
  have hk := mBlock512 (i - 262144) (by omega)
  rwa [show 262144 + (i - 262144) = i by omega] at hk

theorem minUpTo_513 : ∀ i, i < 263168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 262656
  · exact minUpTo_512 i h
  have hk := mBlock513 (i - 262656) (by omega)
  rwa [show 262656 + (i - 262656) = i by omega] at hk

theorem minUpTo_514 : ∀ i, i < 263680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 263168
  · exact minUpTo_513 i h
  have hk := mBlock514 (i - 263168) (by omega)
  rwa [show 263168 + (i - 263168) = i by omega] at hk

theorem minUpTo_515 : ∀ i, i < 264192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 263680
  · exact minUpTo_514 i h
  have hk := mBlock515 (i - 263680) (by omega)
  rwa [show 263680 + (i - 263680) = i by omega] at hk

theorem minUpTo_516 : ∀ i, i < 264704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 264192
  · exact minUpTo_515 i h
  have hk := mBlock516 (i - 264192) (by omega)
  rwa [show 264192 + (i - 264192) = i by omega] at hk

theorem minUpTo_517 : ∀ i, i < 265216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 264704
  · exact minUpTo_516 i h
  have hk := mBlock517 (i - 264704) (by omega)
  rwa [show 264704 + (i - 264704) = i by omega] at hk

theorem minUpTo_518 : ∀ i, i < 265728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 265216
  · exact minUpTo_517 i h
  have hk := mBlock518 (i - 265216) (by omega)
  rwa [show 265216 + (i - 265216) = i by omega] at hk

theorem minUpTo_519 : ∀ i, i < 266240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 265728
  · exact minUpTo_518 i h
  have hk := mBlock519 (i - 265728) (by omega)
  rwa [show 265728 + (i - 265728) = i by omega] at hk

theorem minUpTo_520 : ∀ i, i < 266752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 266240
  · exact minUpTo_519 i h
  have hk := mBlock520 (i - 266240) (by omega)
  rwa [show 266240 + (i - 266240) = i by omega] at hk

theorem minUpTo_521 : ∀ i, i < 267264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 266752
  · exact minUpTo_520 i h
  have hk := mBlock521 (i - 266752) (by omega)
  rwa [show 266752 + (i - 266752) = i by omega] at hk

theorem minUpTo_522 : ∀ i, i < 267776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 267264
  · exact minUpTo_521 i h
  have hk := mBlock522 (i - 267264) (by omega)
  rwa [show 267264 + (i - 267264) = i by omega] at hk

theorem minUpTo_523 : ∀ i, i < 268288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 267776
  · exact minUpTo_522 i h
  have hk := mBlock523 (i - 267776) (by omega)
  rwa [show 267776 + (i - 267776) = i by omega] at hk

theorem minUpTo_524 : ∀ i, i < 268800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 268288
  · exact minUpTo_523 i h
  have hk := mBlock524 (i - 268288) (by omega)
  rwa [show 268288 + (i - 268288) = i by omega] at hk

theorem minUpTo_525 : ∀ i, i < 269312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 268800
  · exact minUpTo_524 i h
  have hk := mBlock525 (i - 268800) (by omega)
  rwa [show 268800 + (i - 268800) = i by omega] at hk

theorem minUpTo_526 : ∀ i, i < 269824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 269312
  · exact minUpTo_525 i h
  have hk := mBlock526 (i - 269312) (by omega)
  rwa [show 269312 + (i - 269312) = i by omega] at hk

theorem minUpTo_527 : ∀ i, i < 270336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 269824
  · exact minUpTo_526 i h
  have hk := mBlock527 (i - 269824) (by omega)
  rwa [show 269824 + (i - 269824) = i by omega] at hk

theorem minUpTo_528 : ∀ i, i < 270848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 270336
  · exact minUpTo_527 i h
  have hk := mBlock528 (i - 270336) (by omega)
  rwa [show 270336 + (i - 270336) = i by omega] at hk

theorem minUpTo_529 : ∀ i, i < 271360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 270848
  · exact minUpTo_528 i h
  have hk := mBlock529 (i - 270848) (by omega)
  rwa [show 270848 + (i - 270848) = i by omega] at hk

theorem minUpTo_530 : ∀ i, i < 271872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 271360
  · exact minUpTo_529 i h
  have hk := mBlock530 (i - 271360) (by omega)
  rwa [show 271360 + (i - 271360) = i by omega] at hk

theorem minUpTo_531 : ∀ i, i < 272384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 271872
  · exact minUpTo_530 i h
  have hk := mBlock531 (i - 271872) (by omega)
  rwa [show 271872 + (i - 271872) = i by omega] at hk

theorem minUpTo_532 : ∀ i, i < 272896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 272384
  · exact minUpTo_531 i h
  have hk := mBlock532 (i - 272384) (by omega)
  rwa [show 272384 + (i - 272384) = i by omega] at hk

theorem minUpTo_533 : ∀ i, i < 273408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 272896
  · exact minUpTo_532 i h
  have hk := mBlock533 (i - 272896) (by omega)
  rwa [show 272896 + (i - 272896) = i by omega] at hk

theorem minUpTo_534 : ∀ i, i < 273920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 273408
  · exact minUpTo_533 i h
  have hk := mBlock534 (i - 273408) (by omega)
  rwa [show 273408 + (i - 273408) = i by omega] at hk

theorem minUpTo_535 : ∀ i, i < 274432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 273920
  · exact minUpTo_534 i h
  have hk := mBlock535 (i - 273920) (by omega)
  rwa [show 273920 + (i - 273920) = i by omega] at hk

theorem minUpTo_536 : ∀ i, i < 274944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 274432
  · exact minUpTo_535 i h
  have hk := mBlock536 (i - 274432) (by omega)
  rwa [show 274432 + (i - 274432) = i by omega] at hk

theorem minUpTo_537 : ∀ i, i < 275456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 274944
  · exact minUpTo_536 i h
  have hk := mBlock537 (i - 274944) (by omega)
  rwa [show 274944 + (i - 274944) = i by omega] at hk

theorem minUpTo_538 : ∀ i, i < 275968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 275456
  · exact minUpTo_537 i h
  have hk := mBlock538 (i - 275456) (by omega)
  rwa [show 275456 + (i - 275456) = i by omega] at hk

theorem minUpTo_539 : ∀ i, i < 276480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 275968
  · exact minUpTo_538 i h
  have hk := mBlock539 (i - 275968) (by omega)
  rwa [show 275968 + (i - 275968) = i by omega] at hk

theorem minUpTo_540 : ∀ i, i < 276992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 276480
  · exact minUpTo_539 i h
  have hk := mBlock540 (i - 276480) (by omega)
  rwa [show 276480 + (i - 276480) = i by omega] at hk

theorem minUpTo_541 : ∀ i, i < 277504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 276992
  · exact minUpTo_540 i h
  have hk := mBlock541 (i - 276992) (by omega)
  rwa [show 276992 + (i - 276992) = i by omega] at hk

theorem minUpTo_542 : ∀ i, i < 278016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 277504
  · exact minUpTo_541 i h
  have hk := mBlock542 (i - 277504) (by omega)
  rwa [show 277504 + (i - 277504) = i by omega] at hk

theorem minUpTo_543 : ∀ i, i < 278528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 278016
  · exact minUpTo_542 i h
  have hk := mBlock543 (i - 278016) (by omega)
  rwa [show 278016 + (i - 278016) = i by omega] at hk

theorem minUpTo_544 : ∀ i, i < 279040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 278528
  · exact minUpTo_543 i h
  have hk := mBlock544 (i - 278528) (by omega)
  rwa [show 278528 + (i - 278528) = i by omega] at hk

theorem minUpTo_545 : ∀ i, i < 279552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 279040
  · exact minUpTo_544 i h
  have hk := mBlock545 (i - 279040) (by omega)
  rwa [show 279040 + (i - 279040) = i by omega] at hk

theorem minUpTo_546 : ∀ i, i < 280064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 279552
  · exact minUpTo_545 i h
  have hk := mBlock546 (i - 279552) (by omega)
  rwa [show 279552 + (i - 279552) = i by omega] at hk

theorem minUpTo_547 : ∀ i, i < 280576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 280064
  · exact minUpTo_546 i h
  have hk := mBlock547 (i - 280064) (by omega)
  rwa [show 280064 + (i - 280064) = i by omega] at hk

theorem minUpTo_548 : ∀ i, i < 281088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 280576
  · exact minUpTo_547 i h
  have hk := mBlock548 (i - 280576) (by omega)
  rwa [show 280576 + (i - 280576) = i by omega] at hk

theorem minUpTo_549 : ∀ i, i < 281600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 281088
  · exact minUpTo_548 i h
  have hk := mBlock549 (i - 281088) (by omega)
  rwa [show 281088 + (i - 281088) = i by omega] at hk

theorem minUpTo_550 : ∀ i, i < 282112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 281600
  · exact minUpTo_549 i h
  have hk := mBlock550 (i - 281600) (by omega)
  rwa [show 281600 + (i - 281600) = i by omega] at hk

theorem minUpTo_551 : ∀ i, i < 282624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 282112
  · exact minUpTo_550 i h
  have hk := mBlock551 (i - 282112) (by omega)
  rwa [show 282112 + (i - 282112) = i by omega] at hk

theorem minUpTo_552 : ∀ i, i < 283136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 282624
  · exact minUpTo_551 i h
  have hk := mBlock552 (i - 282624) (by omega)
  rwa [show 282624 + (i - 282624) = i by omega] at hk

theorem minUpTo_553 : ∀ i, i < 283648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 283136
  · exact minUpTo_552 i h
  have hk := mBlock553 (i - 283136) (by omega)
  rwa [show 283136 + (i - 283136) = i by omega] at hk

theorem minUpTo_554 : ∀ i, i < 284160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 283648
  · exact minUpTo_553 i h
  have hk := mBlock554 (i - 283648) (by omega)
  rwa [show 283648 + (i - 283648) = i by omega] at hk

theorem minUpTo_555 : ∀ i, i < 284672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 284160
  · exact minUpTo_554 i h
  have hk := mBlock555 (i - 284160) (by omega)
  rwa [show 284160 + (i - 284160) = i by omega] at hk

theorem minUpTo_556 : ∀ i, i < 285184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 284672
  · exact minUpTo_555 i h
  have hk := mBlock556 (i - 284672) (by omega)
  rwa [show 284672 + (i - 284672) = i by omega] at hk

theorem minUpTo_557 : ∀ i, i < 285696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 285184
  · exact minUpTo_556 i h
  have hk := mBlock557 (i - 285184) (by omega)
  rwa [show 285184 + (i - 285184) = i by omega] at hk

theorem minUpTo_558 : ∀ i, i < 286208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 285696
  · exact minUpTo_557 i h
  have hk := mBlock558 (i - 285696) (by omega)
  rwa [show 285696 + (i - 285696) = i by omega] at hk

theorem minUpTo_559 : ∀ i, i < 286720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 286208
  · exact minUpTo_558 i h
  have hk := mBlock559 (i - 286208) (by omega)
  rwa [show 286208 + (i - 286208) = i by omega] at hk

theorem minUpTo_560 : ∀ i, i < 287232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 286720
  · exact minUpTo_559 i h
  have hk := mBlock560 (i - 286720) (by omega)
  rwa [show 286720 + (i - 286720) = i by omega] at hk

theorem minUpTo_561 : ∀ i, i < 287744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 287232
  · exact minUpTo_560 i h
  have hk := mBlock561 (i - 287232) (by omega)
  rwa [show 287232 + (i - 287232) = i by omega] at hk

theorem minUpTo_562 : ∀ i, i < 288256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 287744
  · exact minUpTo_561 i h
  have hk := mBlock562 (i - 287744) (by omega)
  rwa [show 287744 + (i - 287744) = i by omega] at hk

theorem minUpTo_563 : ∀ i, i < 288768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 288256
  · exact minUpTo_562 i h
  have hk := mBlock563 (i - 288256) (by omega)
  rwa [show 288256 + (i - 288256) = i by omega] at hk

theorem minUpTo_564 : ∀ i, i < 289280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 288768
  · exact minUpTo_563 i h
  have hk := mBlock564 (i - 288768) (by omega)
  rwa [show 288768 + (i - 288768) = i by omega] at hk

theorem minUpTo_565 : ∀ i, i < 289792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 289280
  · exact minUpTo_564 i h
  have hk := mBlock565 (i - 289280) (by omega)
  rwa [show 289280 + (i - 289280) = i by omega] at hk

theorem minUpTo_566 : ∀ i, i < 290304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 289792
  · exact minUpTo_565 i h
  have hk := mBlock566 (i - 289792) (by omega)
  rwa [show 289792 + (i - 289792) = i by omega] at hk

theorem minUpTo_567 : ∀ i, i < 290816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 290304
  · exact minUpTo_566 i h
  have hk := mBlock567 (i - 290304) (by omega)
  rwa [show 290304 + (i - 290304) = i by omega] at hk

theorem minUpTo_568 : ∀ i, i < 291328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 290816
  · exact minUpTo_567 i h
  have hk := mBlock568 (i - 290816) (by omega)
  rwa [show 290816 + (i - 290816) = i by omega] at hk

theorem minUpTo_569 : ∀ i, i < 291840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 291328
  · exact minUpTo_568 i h
  have hk := mBlock569 (i - 291328) (by omega)
  rwa [show 291328 + (i - 291328) = i by omega] at hk

theorem minUpTo_570 : ∀ i, i < 292352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 291840
  · exact minUpTo_569 i h
  have hk := mBlock570 (i - 291840) (by omega)
  rwa [show 291840 + (i - 291840) = i by omega] at hk

theorem minUpTo_571 : ∀ i, i < 292864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 292352
  · exact minUpTo_570 i h
  have hk := mBlock571 (i - 292352) (by omega)
  rwa [show 292352 + (i - 292352) = i by omega] at hk

theorem minUpTo_572 : ∀ i, i < 293376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 292864
  · exact minUpTo_571 i h
  have hk := mBlock572 (i - 292864) (by omega)
  rwa [show 292864 + (i - 292864) = i by omega] at hk

theorem minUpTo_573 : ∀ i, i < 293888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 293376
  · exact minUpTo_572 i h
  have hk := mBlock573 (i - 293376) (by omega)
  rwa [show 293376 + (i - 293376) = i by omega] at hk

theorem minUpTo_574 : ∀ i, i < 294400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 293888
  · exact minUpTo_573 i h
  have hk := mBlock574 (i - 293888) (by omega)
  rwa [show 293888 + (i - 293888) = i by omega] at hk

theorem minUpTo_575 : ∀ i, i < 294912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 294400
  · exact minUpTo_574 i h
  have hk := mBlock575 (i - 294400) (by omega)
  rwa [show 294400 + (i - 294400) = i by omega] at hk

theorem minUpTo_576 : ∀ i, i < 295424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 294912
  · exact minUpTo_575 i h
  have hk := mBlock576 (i - 294912) (by omega)
  rwa [show 294912 + (i - 294912) = i by omega] at hk

theorem minUpTo_577 : ∀ i, i < 295936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 295424
  · exact minUpTo_576 i h
  have hk := mBlock577 (i - 295424) (by omega)
  rwa [show 295424 + (i - 295424) = i by omega] at hk

theorem minUpTo_578 : ∀ i, i < 296448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 295936
  · exact minUpTo_577 i h
  have hk := mBlock578 (i - 295936) (by omega)
  rwa [show 295936 + (i - 295936) = i by omega] at hk

theorem minUpTo_579 : ∀ i, i < 296960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 296448
  · exact minUpTo_578 i h
  have hk := mBlock579 (i - 296448) (by omega)
  rwa [show 296448 + (i - 296448) = i by omega] at hk

theorem minUpTo_580 : ∀ i, i < 297472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 296960
  · exact minUpTo_579 i h
  have hk := mBlock580 (i - 296960) (by omega)
  rwa [show 296960 + (i - 296960) = i by omega] at hk

theorem minUpTo_581 : ∀ i, i < 297984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 297472
  · exact minUpTo_580 i h
  have hk := mBlock581 (i - 297472) (by omega)
  rwa [show 297472 + (i - 297472) = i by omega] at hk

theorem minUpTo_582 : ∀ i, i < 298496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 297984
  · exact minUpTo_581 i h
  have hk := mBlock582 (i - 297984) (by omega)
  rwa [show 297984 + (i - 297984) = i by omega] at hk

theorem minUpTo_583 : ∀ i, i < 299008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 298496
  · exact minUpTo_582 i h
  have hk := mBlock583 (i - 298496) (by omega)
  rwa [show 298496 + (i - 298496) = i by omega] at hk

theorem minUpTo_584 : ∀ i, i < 299520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 299008
  · exact minUpTo_583 i h
  have hk := mBlock584 (i - 299008) (by omega)
  rwa [show 299008 + (i - 299008) = i by omega] at hk

theorem minUpTo_585 : ∀ i, i < 300032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 299520
  · exact minUpTo_584 i h
  have hk := mBlock585 (i - 299520) (by omega)
  rwa [show 299520 + (i - 299520) = i by omega] at hk

theorem minUpTo_586 : ∀ i, i < 300544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 300032
  · exact minUpTo_585 i h
  have hk := mBlock586 (i - 300032) (by omega)
  rwa [show 300032 + (i - 300032) = i by omega] at hk

theorem minUpTo_587 : ∀ i, i < 301056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 300544
  · exact minUpTo_586 i h
  have hk := mBlock587 (i - 300544) (by omega)
  rwa [show 300544 + (i - 300544) = i by omega] at hk

theorem minUpTo_588 : ∀ i, i < 301568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 301056
  · exact minUpTo_587 i h
  have hk := mBlock588 (i - 301056) (by omega)
  rwa [show 301056 + (i - 301056) = i by omega] at hk

theorem minUpTo_589 : ∀ i, i < 302080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 301568
  · exact minUpTo_588 i h
  have hk := mBlock589 (i - 301568) (by omega)
  rwa [show 301568 + (i - 301568) = i by omega] at hk

theorem minUpTo_590 : ∀ i, i < 302592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 302080
  · exact minUpTo_589 i h
  have hk := mBlock590 (i - 302080) (by omega)
  rwa [show 302080 + (i - 302080) = i by omega] at hk

theorem minUpTo_591 : ∀ i, i < 303104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 302592
  · exact minUpTo_590 i h
  have hk := mBlock591 (i - 302592) (by omega)
  rwa [show 302592 + (i - 302592) = i by omega] at hk

theorem minUpTo_592 : ∀ i, i < 303616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 303104
  · exact minUpTo_591 i h
  have hk := mBlock592 (i - 303104) (by omega)
  rwa [show 303104 + (i - 303104) = i by omega] at hk

theorem minUpTo_593 : ∀ i, i < 304128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 303616
  · exact minUpTo_592 i h
  have hk := mBlock593 (i - 303616) (by omega)
  rwa [show 303616 + (i - 303616) = i by omega] at hk

theorem minUpTo_594 : ∀ i, i < 304640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 304128
  · exact minUpTo_593 i h
  have hk := mBlock594 (i - 304128) (by omega)
  rwa [show 304128 + (i - 304128) = i by omega] at hk

theorem minUpTo_595 : ∀ i, i < 305152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 304640
  · exact minUpTo_594 i h
  have hk := mBlock595 (i - 304640) (by omega)
  rwa [show 304640 + (i - 304640) = i by omega] at hk

theorem minUpTo_596 : ∀ i, i < 305664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 305152
  · exact minUpTo_595 i h
  have hk := mBlock596 (i - 305152) (by omega)
  rwa [show 305152 + (i - 305152) = i by omega] at hk

theorem minUpTo_597 : ∀ i, i < 306176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 305664
  · exact minUpTo_596 i h
  have hk := mBlock597 (i - 305664) (by omega)
  rwa [show 305664 + (i - 305664) = i by omega] at hk

theorem minUpTo_598 : ∀ i, i < 306688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 306176
  · exact minUpTo_597 i h
  have hk := mBlock598 (i - 306176) (by omega)
  rwa [show 306176 + (i - 306176) = i by omega] at hk

theorem minUpTo_599 : ∀ i, i < 307200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 306688
  · exact minUpTo_598 i h
  have hk := mBlock599 (i - 306688) (by omega)
  rwa [show 306688 + (i - 306688) = i by omega] at hk

theorem minUpTo_600 : ∀ i, i < 307712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 307200
  · exact minUpTo_599 i h
  have hk := mBlock600 (i - 307200) (by omega)
  rwa [show 307200 + (i - 307200) = i by omega] at hk

theorem minUpTo_601 : ∀ i, i < 308224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 307712
  · exact minUpTo_600 i h
  have hk := mBlock601 (i - 307712) (by omega)
  rwa [show 307712 + (i - 307712) = i by omega] at hk

theorem minUpTo_602 : ∀ i, i < 308736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 308224
  · exact minUpTo_601 i h
  have hk := mBlock602 (i - 308224) (by omega)
  rwa [show 308224 + (i - 308224) = i by omega] at hk

theorem minUpTo_603 : ∀ i, i < 309248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 308736
  · exact minUpTo_602 i h
  have hk := mBlock603 (i - 308736) (by omega)
  rwa [show 308736 + (i - 308736) = i by omega] at hk

theorem minUpTo_604 : ∀ i, i < 309760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 309248
  · exact minUpTo_603 i h
  have hk := mBlock604 (i - 309248) (by omega)
  rwa [show 309248 + (i - 309248) = i by omega] at hk

theorem minUpTo_605 : ∀ i, i < 310272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 309760
  · exact minUpTo_604 i h
  have hk := mBlock605 (i - 309760) (by omega)
  rwa [show 309760 + (i - 309760) = i by omega] at hk

theorem minUpTo_606 : ∀ i, i < 310784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 310272
  · exact minUpTo_605 i h
  have hk := mBlock606 (i - 310272) (by omega)
  rwa [show 310272 + (i - 310272) = i by omega] at hk

theorem minUpTo_607 : ∀ i, i < 311296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 310784
  · exact minUpTo_606 i h
  have hk := mBlock607 (i - 310784) (by omega)
  rwa [show 310784 + (i - 310784) = i by omega] at hk

theorem minUpTo_608 : ∀ i, i < 311808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 311296
  · exact minUpTo_607 i h
  have hk := mBlock608 (i - 311296) (by omega)
  rwa [show 311296 + (i - 311296) = i by omega] at hk

theorem minUpTo_609 : ∀ i, i < 312320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 311808
  · exact minUpTo_608 i h
  have hk := mBlock609 (i - 311808) (by omega)
  rwa [show 311808 + (i - 311808) = i by omega] at hk

theorem minUpTo_610 : ∀ i, i < 312832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 312320
  · exact minUpTo_609 i h
  have hk := mBlock610 (i - 312320) (by omega)
  rwa [show 312320 + (i - 312320) = i by omega] at hk

theorem minUpTo_611 : ∀ i, i < 313344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 312832
  · exact minUpTo_610 i h
  have hk := mBlock611 (i - 312832) (by omega)
  rwa [show 312832 + (i - 312832) = i by omega] at hk

theorem minUpTo_612 : ∀ i, i < 313856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 313344
  · exact minUpTo_611 i h
  have hk := mBlock612 (i - 313344) (by omega)
  rwa [show 313344 + (i - 313344) = i by omega] at hk

theorem minUpTo_613 : ∀ i, i < 314368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 313856
  · exact minUpTo_612 i h
  have hk := mBlock613 (i - 313856) (by omega)
  rwa [show 313856 + (i - 313856) = i by omega] at hk

theorem minUpTo_614 : ∀ i, i < 314880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 314368
  · exact minUpTo_613 i h
  have hk := mBlock614 (i - 314368) (by omega)
  rwa [show 314368 + (i - 314368) = i by omega] at hk

theorem minUpTo_615 : ∀ i, i < 315392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 314880
  · exact minUpTo_614 i h
  have hk := mBlock615 (i - 314880) (by omega)
  rwa [show 314880 + (i - 314880) = i by omega] at hk

theorem minUpTo_616 : ∀ i, i < 315904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 315392
  · exact minUpTo_615 i h
  have hk := mBlock616 (i - 315392) (by omega)
  rwa [show 315392 + (i - 315392) = i by omega] at hk

theorem minUpTo_617 : ∀ i, i < 316416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 315904
  · exact minUpTo_616 i h
  have hk := mBlock617 (i - 315904) (by omega)
  rwa [show 315904 + (i - 315904) = i by omega] at hk

theorem minUpTo_618 : ∀ i, i < 316928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 316416
  · exact minUpTo_617 i h
  have hk := mBlock618 (i - 316416) (by omega)
  rwa [show 316416 + (i - 316416) = i by omega] at hk

theorem minUpTo_619 : ∀ i, i < 317440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 316928
  · exact minUpTo_618 i h
  have hk := mBlock619 (i - 316928) (by omega)
  rwa [show 316928 + (i - 316928) = i by omega] at hk

theorem minUpTo_620 : ∀ i, i < 317952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 317440
  · exact minUpTo_619 i h
  have hk := mBlock620 (i - 317440) (by omega)
  rwa [show 317440 + (i - 317440) = i by omega] at hk

theorem minUpTo_621 : ∀ i, i < 318464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 317952
  · exact minUpTo_620 i h
  have hk := mBlock621 (i - 317952) (by omega)
  rwa [show 317952 + (i - 317952) = i by omega] at hk

theorem minUpTo_622 : ∀ i, i < 318976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 318464
  · exact minUpTo_621 i h
  have hk := mBlock622 (i - 318464) (by omega)
  rwa [show 318464 + (i - 318464) = i by omega] at hk

theorem minUpTo_623 : ∀ i, i < 319488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 318976
  · exact minUpTo_622 i h
  have hk := mBlock623 (i - 318976) (by omega)
  rwa [show 318976 + (i - 318976) = i by omega] at hk

theorem minUpTo_624 : ∀ i, i < 320000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 319488
  · exact minUpTo_623 i h
  have hk := mBlock624 (i - 319488) (by omega)
  rwa [show 319488 + (i - 319488) = i by omega] at hk

theorem minUpTo_625 : ∀ i, i < 320512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 320000
  · exact minUpTo_624 i h
  have hk := mBlock625 (i - 320000) (by omega)
  rwa [show 320000 + (i - 320000) = i by omega] at hk

theorem minUpTo_626 : ∀ i, i < 321024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 320512
  · exact minUpTo_625 i h
  have hk := mBlock626 (i - 320512) (by omega)
  rwa [show 320512 + (i - 320512) = i by omega] at hk

theorem minUpTo_627 : ∀ i, i < 321536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 321024
  · exact minUpTo_626 i h
  have hk := mBlock627 (i - 321024) (by omega)
  rwa [show 321024 + (i - 321024) = i by omega] at hk

theorem minUpTo_628 : ∀ i, i < 322048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 321536
  · exact minUpTo_627 i h
  have hk := mBlock628 (i - 321536) (by omega)
  rwa [show 321536 + (i - 321536) = i by omega] at hk

theorem minUpTo_629 : ∀ i, i < 322560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 322048
  · exact minUpTo_628 i h
  have hk := mBlock629 (i - 322048) (by omega)
  rwa [show 322048 + (i - 322048) = i by omega] at hk

theorem minUpTo_630 : ∀ i, i < 323072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 322560
  · exact minUpTo_629 i h
  have hk := mBlock630 (i - 322560) (by omega)
  rwa [show 322560 + (i - 322560) = i by omega] at hk

theorem minUpTo_631 : ∀ i, i < 323584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 323072
  · exact minUpTo_630 i h
  have hk := mBlock631 (i - 323072) (by omega)
  rwa [show 323072 + (i - 323072) = i by omega] at hk

theorem minUpTo_632 : ∀ i, i < 324096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 323584
  · exact minUpTo_631 i h
  have hk := mBlock632 (i - 323584) (by omega)
  rwa [show 323584 + (i - 323584) = i by omega] at hk

theorem minUpTo_633 : ∀ i, i < 324608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 324096
  · exact minUpTo_632 i h
  have hk := mBlock633 (i - 324096) (by omega)
  rwa [show 324096 + (i - 324096) = i by omega] at hk

theorem minUpTo_634 : ∀ i, i < 325120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 324608
  · exact minUpTo_633 i h
  have hk := mBlock634 (i - 324608) (by omega)
  rwa [show 324608 + (i - 324608) = i by omega] at hk

theorem minUpTo_635 : ∀ i, i < 325632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 325120
  · exact minUpTo_634 i h
  have hk := mBlock635 (i - 325120) (by omega)
  rwa [show 325120 + (i - 325120) = i by omega] at hk

theorem minUpTo_636 : ∀ i, i < 326144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 325632
  · exact minUpTo_635 i h
  have hk := mBlock636 (i - 325632) (by omega)
  rwa [show 325632 + (i - 325632) = i by omega] at hk

theorem minUpTo_637 : ∀ i, i < 326656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 326144
  · exact minUpTo_636 i h
  have hk := mBlock637 (i - 326144) (by omega)
  rwa [show 326144 + (i - 326144) = i by omega] at hk

theorem minUpTo_638 : ∀ i, i < 327168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 326656
  · exact minUpTo_637 i h
  have hk := mBlock638 (i - 326656) (by omega)
  rwa [show 326656 + (i - 326656) = i by omega] at hk

theorem minUpTo_639 : ∀ i, i < 327680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 327168
  · exact minUpTo_638 i h
  have hk := mBlock639 (i - 327168) (by omega)
  rwa [show 327168 + (i - 327168) = i by omega] at hk

theorem minUpTo_640 : ∀ i, i < 328192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 327680
  · exact minUpTo_639 i h
  have hk := mBlock640 (i - 327680) (by omega)
  rwa [show 327680 + (i - 327680) = i by omega] at hk

theorem minUpTo_641 : ∀ i, i < 328704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 328192
  · exact minUpTo_640 i h
  have hk := mBlock641 (i - 328192) (by omega)
  rwa [show 328192 + (i - 328192) = i by omega] at hk

theorem minUpTo_642 : ∀ i, i < 329216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 328704
  · exact minUpTo_641 i h
  have hk := mBlock642 (i - 328704) (by omega)
  rwa [show 328704 + (i - 328704) = i by omega] at hk

theorem minUpTo_643 : ∀ i, i < 329728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 329216
  · exact minUpTo_642 i h
  have hk := mBlock643 (i - 329216) (by omega)
  rwa [show 329216 + (i - 329216) = i by omega] at hk

theorem minUpTo_644 : ∀ i, i < 330240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 329728
  · exact minUpTo_643 i h
  have hk := mBlock644 (i - 329728) (by omega)
  rwa [show 329728 + (i - 329728) = i by omega] at hk

theorem minUpTo_645 : ∀ i, i < 330752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 330240
  · exact minUpTo_644 i h
  have hk := mBlock645 (i - 330240) (by omega)
  rwa [show 330240 + (i - 330240) = i by omega] at hk

theorem minUpTo_646 : ∀ i, i < 331264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 330752
  · exact minUpTo_645 i h
  have hk := mBlock646 (i - 330752) (by omega)
  rwa [show 330752 + (i - 330752) = i by omega] at hk

theorem minUpTo_647 : ∀ i, i < 331776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 331264
  · exact minUpTo_646 i h
  have hk := mBlock647 (i - 331264) (by omega)
  rwa [show 331264 + (i - 331264) = i by omega] at hk

theorem minUpTo_648 : ∀ i, i < 332288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 331776
  · exact minUpTo_647 i h
  have hk := mBlock648 (i - 331776) (by omega)
  rwa [show 331776 + (i - 331776) = i by omega] at hk

theorem minUpTo_649 : ∀ i, i < 332800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 332288
  · exact minUpTo_648 i h
  have hk := mBlock649 (i - 332288) (by omega)
  rwa [show 332288 + (i - 332288) = i by omega] at hk

theorem minUpTo_650 : ∀ i, i < 333312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 332800
  · exact minUpTo_649 i h
  have hk := mBlock650 (i - 332800) (by omega)
  rwa [show 332800 + (i - 332800) = i by omega] at hk

theorem minUpTo_651 : ∀ i, i < 333824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 333312
  · exact minUpTo_650 i h
  have hk := mBlock651 (i - 333312) (by omega)
  rwa [show 333312 + (i - 333312) = i by omega] at hk

theorem minUpTo_652 : ∀ i, i < 334336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 333824
  · exact minUpTo_651 i h
  have hk := mBlock652 (i - 333824) (by omega)
  rwa [show 333824 + (i - 333824) = i by omega] at hk

theorem minUpTo_653 : ∀ i, i < 334848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 334336
  · exact minUpTo_652 i h
  have hk := mBlock653 (i - 334336) (by omega)
  rwa [show 334336 + (i - 334336) = i by omega] at hk

theorem minUpTo_654 : ∀ i, i < 335360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 334848
  · exact minUpTo_653 i h
  have hk := mBlock654 (i - 334848) (by omega)
  rwa [show 334848 + (i - 334848) = i by omega] at hk

theorem minUpTo_655 : ∀ i, i < 335872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 335360
  · exact minUpTo_654 i h
  have hk := mBlock655 (i - 335360) (by omega)
  rwa [show 335360 + (i - 335360) = i by omega] at hk

theorem minUpTo_656 : ∀ i, i < 336384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 335872
  · exact minUpTo_655 i h
  have hk := mBlock656 (i - 335872) (by omega)
  rwa [show 335872 + (i - 335872) = i by omega] at hk

theorem minUpTo_657 : ∀ i, i < 336896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 336384
  · exact minUpTo_656 i h
  have hk := mBlock657 (i - 336384) (by omega)
  rwa [show 336384 + (i - 336384) = i by omega] at hk

theorem minUpTo_658 : ∀ i, i < 337408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 336896
  · exact minUpTo_657 i h
  have hk := mBlock658 (i - 336896) (by omega)
  rwa [show 336896 + (i - 336896) = i by omega] at hk

theorem minUpTo_659 : ∀ i, i < 337920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 337408
  · exact minUpTo_658 i h
  have hk := mBlock659 (i - 337408) (by omega)
  rwa [show 337408 + (i - 337408) = i by omega] at hk

theorem minUpTo_660 : ∀ i, i < 338432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 337920
  · exact minUpTo_659 i h
  have hk := mBlock660 (i - 337920) (by omega)
  rwa [show 337920 + (i - 337920) = i by omega] at hk

theorem minUpTo_661 : ∀ i, i < 338944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 338432
  · exact minUpTo_660 i h
  have hk := mBlock661 (i - 338432) (by omega)
  rwa [show 338432 + (i - 338432) = i by omega] at hk

theorem minUpTo_662 : ∀ i, i < 339456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 338944
  · exact minUpTo_661 i h
  have hk := mBlock662 (i - 338944) (by omega)
  rwa [show 338944 + (i - 338944) = i by omega] at hk

theorem minUpTo_663 : ∀ i, i < 339968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 339456
  · exact minUpTo_662 i h
  have hk := mBlock663 (i - 339456) (by omega)
  rwa [show 339456 + (i - 339456) = i by omega] at hk

theorem minUpTo_664 : ∀ i, i < 340480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 339968
  · exact minUpTo_663 i h
  have hk := mBlock664 (i - 339968) (by omega)
  rwa [show 339968 + (i - 339968) = i by omega] at hk

theorem minUpTo_665 : ∀ i, i < 340992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 340480
  · exact minUpTo_664 i h
  have hk := mBlock665 (i - 340480) (by omega)
  rwa [show 340480 + (i - 340480) = i by omega] at hk

theorem minUpTo_666 : ∀ i, i < 341504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 340992
  · exact minUpTo_665 i h
  have hk := mBlock666 (i - 340992) (by omega)
  rwa [show 340992 + (i - 340992) = i by omega] at hk

theorem minUpTo_667 : ∀ i, i < 342016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 341504
  · exact minUpTo_666 i h
  have hk := mBlock667 (i - 341504) (by omega)
  rwa [show 341504 + (i - 341504) = i by omega] at hk

theorem minUpTo_668 : ∀ i, i < 342528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 342016
  · exact minUpTo_667 i h
  have hk := mBlock668 (i - 342016) (by omega)
  rwa [show 342016 + (i - 342016) = i by omega] at hk

theorem minUpTo_669 : ∀ i, i < 343040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 342528
  · exact minUpTo_668 i h
  have hk := mBlock669 (i - 342528) (by omega)
  rwa [show 342528 + (i - 342528) = i by omega] at hk

theorem minUpTo_670 : ∀ i, i < 343552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 343040
  · exact minUpTo_669 i h
  have hk := mBlock670 (i - 343040) (by omega)
  rwa [show 343040 + (i - 343040) = i by omega] at hk

theorem minUpTo_671 : ∀ i, i < 344064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 343552
  · exact minUpTo_670 i h
  have hk := mBlock671 (i - 343552) (by omega)
  rwa [show 343552 + (i - 343552) = i by omega] at hk

theorem minUpTo_672 : ∀ i, i < 344576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 344064
  · exact minUpTo_671 i h
  have hk := mBlock672 (i - 344064) (by omega)
  rwa [show 344064 + (i - 344064) = i by omega] at hk

theorem minUpTo_673 : ∀ i, i < 345088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 344576
  · exact minUpTo_672 i h
  have hk := mBlock673 (i - 344576) (by omega)
  rwa [show 344576 + (i - 344576) = i by omega] at hk

theorem minUpTo_674 : ∀ i, i < 345600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 345088
  · exact minUpTo_673 i h
  have hk := mBlock674 (i - 345088) (by omega)
  rwa [show 345088 + (i - 345088) = i by omega] at hk

theorem minUpTo_675 : ∀ i, i < 346112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 345600
  · exact minUpTo_674 i h
  have hk := mBlock675 (i - 345600) (by omega)
  rwa [show 345600 + (i - 345600) = i by omega] at hk

theorem minUpTo_676 : ∀ i, i < 346624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 346112
  · exact minUpTo_675 i h
  have hk := mBlock676 (i - 346112) (by omega)
  rwa [show 346112 + (i - 346112) = i by omega] at hk

theorem minUpTo_677 : ∀ i, i < 347136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 346624
  · exact minUpTo_676 i h
  have hk := mBlock677 (i - 346624) (by omega)
  rwa [show 346624 + (i - 346624) = i by omega] at hk

theorem minUpTo_678 : ∀ i, i < 347648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 347136
  · exact minUpTo_677 i h
  have hk := mBlock678 (i - 347136) (by omega)
  rwa [show 347136 + (i - 347136) = i by omega] at hk

theorem minUpTo_679 : ∀ i, i < 348160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 347648
  · exact minUpTo_678 i h
  have hk := mBlock679 (i - 347648) (by omega)
  rwa [show 347648 + (i - 347648) = i by omega] at hk

theorem minUpTo_680 : ∀ i, i < 348672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 348160
  · exact minUpTo_679 i h
  have hk := mBlock680 (i - 348160) (by omega)
  rwa [show 348160 + (i - 348160) = i by omega] at hk

theorem minUpTo_681 : ∀ i, i < 349184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 348672
  · exact minUpTo_680 i h
  have hk := mBlock681 (i - 348672) (by omega)
  rwa [show 348672 + (i - 348672) = i by omega] at hk

theorem minUpTo_682 : ∀ i, i < 349696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 349184
  · exact minUpTo_681 i h
  have hk := mBlock682 (i - 349184) (by omega)
  rwa [show 349184 + (i - 349184) = i by omega] at hk

theorem minUpTo_683 : ∀ i, i < 350208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 349696
  · exact minUpTo_682 i h
  have hk := mBlock683 (i - 349696) (by omega)
  rwa [show 349696 + (i - 349696) = i by omega] at hk

theorem minUpTo_684 : ∀ i, i < 350720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 350208
  · exact minUpTo_683 i h
  have hk := mBlock684 (i - 350208) (by omega)
  rwa [show 350208 + (i - 350208) = i by omega] at hk

theorem minUpTo_685 : ∀ i, i < 351232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 350720
  · exact minUpTo_684 i h
  have hk := mBlock685 (i - 350720) (by omega)
  rwa [show 350720 + (i - 350720) = i by omega] at hk

theorem minUpTo_686 : ∀ i, i < 351744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 351232
  · exact minUpTo_685 i h
  have hk := mBlock686 (i - 351232) (by omega)
  rwa [show 351232 + (i - 351232) = i by omega] at hk

theorem minUpTo_687 : ∀ i, i < 352256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 351744
  · exact minUpTo_686 i h
  have hk := mBlock687 (i - 351744) (by omega)
  rwa [show 351744 + (i - 351744) = i by omega] at hk

theorem minUpTo_688 : ∀ i, i < 352768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 352256
  · exact minUpTo_687 i h
  have hk := mBlock688 (i - 352256) (by omega)
  rwa [show 352256 + (i - 352256) = i by omega] at hk

theorem minUpTo_689 : ∀ i, i < 353280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 352768
  · exact minUpTo_688 i h
  have hk := mBlock689 (i - 352768) (by omega)
  rwa [show 352768 + (i - 352768) = i by omega] at hk

theorem minUpTo_690 : ∀ i, i < 353792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 353280
  · exact minUpTo_689 i h
  have hk := mBlock690 (i - 353280) (by omega)
  rwa [show 353280 + (i - 353280) = i by omega] at hk

theorem minUpTo_691 : ∀ i, i < 354304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 353792
  · exact minUpTo_690 i h
  have hk := mBlock691 (i - 353792) (by omega)
  rwa [show 353792 + (i - 353792) = i by omega] at hk

theorem minUpTo_692 : ∀ i, i < 354816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 354304
  · exact minUpTo_691 i h
  have hk := mBlock692 (i - 354304) (by omega)
  rwa [show 354304 + (i - 354304) = i by omega] at hk

theorem minUpTo_693 : ∀ i, i < 355328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 354816
  · exact minUpTo_692 i h
  have hk := mBlock693 (i - 354816) (by omega)
  rwa [show 354816 + (i - 354816) = i by omega] at hk

theorem minUpTo_694 : ∀ i, i < 355840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 355328
  · exact minUpTo_693 i h
  have hk := mBlock694 (i - 355328) (by omega)
  rwa [show 355328 + (i - 355328) = i by omega] at hk

theorem minUpTo_695 : ∀ i, i < 356352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 355840
  · exact minUpTo_694 i h
  have hk := mBlock695 (i - 355840) (by omega)
  rwa [show 355840 + (i - 355840) = i by omega] at hk

theorem minUpTo_696 : ∀ i, i < 356864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 356352
  · exact minUpTo_695 i h
  have hk := mBlock696 (i - 356352) (by omega)
  rwa [show 356352 + (i - 356352) = i by omega] at hk

theorem minUpTo_697 : ∀ i, i < 357376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 356864
  · exact minUpTo_696 i h
  have hk := mBlock697 (i - 356864) (by omega)
  rwa [show 356864 + (i - 356864) = i by omega] at hk

theorem minUpTo_698 : ∀ i, i < 357888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 357376
  · exact minUpTo_697 i h
  have hk := mBlock698 (i - 357376) (by omega)
  rwa [show 357376 + (i - 357376) = i by omega] at hk

theorem minUpTo_699 : ∀ i, i < 358400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 357888
  · exact minUpTo_698 i h
  have hk := mBlock699 (i - 357888) (by omega)
  rwa [show 357888 + (i - 357888) = i by omega] at hk

theorem minUpTo_700 : ∀ i, i < 358912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 358400
  · exact minUpTo_699 i h
  have hk := mBlock700 (i - 358400) (by omega)
  rwa [show 358400 + (i - 358400) = i by omega] at hk

theorem minUpTo_701 : ∀ i, i < 359424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 358912
  · exact minUpTo_700 i h
  have hk := mBlock701 (i - 358912) (by omega)
  rwa [show 358912 + (i - 358912) = i by omega] at hk

theorem minUpTo_702 : ∀ i, i < 359936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 359424
  · exact minUpTo_701 i h
  have hk := mBlock702 (i - 359424) (by omega)
  rwa [show 359424 + (i - 359424) = i by omega] at hk

theorem minUpTo_703 : ∀ i, i < 360448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 359936
  · exact minUpTo_702 i h
  have hk := mBlock703 (i - 359936) (by omega)
  rwa [show 359936 + (i - 359936) = i by omega] at hk

theorem minUpTo_704 : ∀ i, i < 360960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 360448
  · exact minUpTo_703 i h
  have hk := mBlock704 (i - 360448) (by omega)
  rwa [show 360448 + (i - 360448) = i by omega] at hk

theorem minUpTo_705 : ∀ i, i < 361472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 360960
  · exact minUpTo_704 i h
  have hk := mBlock705 (i - 360960) (by omega)
  rwa [show 360960 + (i - 360960) = i by omega] at hk

theorem minUpTo_706 : ∀ i, i < 361984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 361472
  · exact minUpTo_705 i h
  have hk := mBlock706 (i - 361472) (by omega)
  rwa [show 361472 + (i - 361472) = i by omega] at hk

theorem minUpTo_707 : ∀ i, i < 362496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 361984
  · exact minUpTo_706 i h
  have hk := mBlock707 (i - 361984) (by omega)
  rwa [show 361984 + (i - 361984) = i by omega] at hk

theorem minUpTo_708 : ∀ i, i < 363008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 362496
  · exact minUpTo_707 i h
  have hk := mBlock708 (i - 362496) (by omega)
  rwa [show 362496 + (i - 362496) = i by omega] at hk

theorem minUpTo_709 : ∀ i, i < 363520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 363008
  · exact minUpTo_708 i h
  have hk := mBlock709 (i - 363008) (by omega)
  rwa [show 363008 + (i - 363008) = i by omega] at hk

theorem minUpTo_710 : ∀ i, i < 364032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 363520
  · exact minUpTo_709 i h
  have hk := mBlock710 (i - 363520) (by omega)
  rwa [show 363520 + (i - 363520) = i by omega] at hk

theorem minUpTo_711 : ∀ i, i < 364544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 364032
  · exact minUpTo_710 i h
  have hk := mBlock711 (i - 364032) (by omega)
  rwa [show 364032 + (i - 364032) = i by omega] at hk

theorem minUpTo_712 : ∀ i, i < 365056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 364544
  · exact minUpTo_711 i h
  have hk := mBlock712 (i - 364544) (by omega)
  rwa [show 364544 + (i - 364544) = i by omega] at hk

theorem minUpTo_713 : ∀ i, i < 365568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 365056
  · exact minUpTo_712 i h
  have hk := mBlock713 (i - 365056) (by omega)
  rwa [show 365056 + (i - 365056) = i by omega] at hk

theorem minUpTo_714 : ∀ i, i < 366080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 365568
  · exact minUpTo_713 i h
  have hk := mBlock714 (i - 365568) (by omega)
  rwa [show 365568 + (i - 365568) = i by omega] at hk

theorem minUpTo_715 : ∀ i, i < 366592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 366080
  · exact minUpTo_714 i h
  have hk := mBlock715 (i - 366080) (by omega)
  rwa [show 366080 + (i - 366080) = i by omega] at hk

theorem minUpTo_716 : ∀ i, i < 367104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 366592
  · exact minUpTo_715 i h
  have hk := mBlock716 (i - 366592) (by omega)
  rwa [show 366592 + (i - 366592) = i by omega] at hk

theorem minUpTo_717 : ∀ i, i < 367616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 367104
  · exact minUpTo_716 i h
  have hk := mBlock717 (i - 367104) (by omega)
  rwa [show 367104 + (i - 367104) = i by omega] at hk

theorem minUpTo_718 : ∀ i, i < 368128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 367616
  · exact minUpTo_717 i h
  have hk := mBlock718 (i - 367616) (by omega)
  rwa [show 367616 + (i - 367616) = i by omega] at hk

theorem minUpTo_719 : ∀ i, i < 368640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 368128
  · exact minUpTo_718 i h
  have hk := mBlock719 (i - 368128) (by omega)
  rwa [show 368128 + (i - 368128) = i by omega] at hk

theorem minUpTo_720 : ∀ i, i < 369152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 368640
  · exact minUpTo_719 i h
  have hk := mBlock720 (i - 368640) (by omega)
  rwa [show 368640 + (i - 368640) = i by omega] at hk

theorem minUpTo_721 : ∀ i, i < 369664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 369152
  · exact minUpTo_720 i h
  have hk := mBlock721 (i - 369152) (by omega)
  rwa [show 369152 + (i - 369152) = i by omega] at hk

theorem minUpTo_722 : ∀ i, i < 370176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 369664
  · exact minUpTo_721 i h
  have hk := mBlock722 (i - 369664) (by omega)
  rwa [show 369664 + (i - 369664) = i by omega] at hk

theorem minUpTo_723 : ∀ i, i < 370688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 370176
  · exact minUpTo_722 i h
  have hk := mBlock723 (i - 370176) (by omega)
  rwa [show 370176 + (i - 370176) = i by omega] at hk

theorem minUpTo_724 : ∀ i, i < 371200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 370688
  · exact minUpTo_723 i h
  have hk := mBlock724 (i - 370688) (by omega)
  rwa [show 370688 + (i - 370688) = i by omega] at hk

theorem minUpTo_725 : ∀ i, i < 371712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 371200
  · exact minUpTo_724 i h
  have hk := mBlock725 (i - 371200) (by omega)
  rwa [show 371200 + (i - 371200) = i by omega] at hk

theorem minUpTo_726 : ∀ i, i < 372224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 371712
  · exact minUpTo_725 i h
  have hk := mBlock726 (i - 371712) (by omega)
  rwa [show 371712 + (i - 371712) = i by omega] at hk

theorem minUpTo_727 : ∀ i, i < 372736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 372224
  · exact minUpTo_726 i h
  have hk := mBlock727 (i - 372224) (by omega)
  rwa [show 372224 + (i - 372224) = i by omega] at hk

theorem minUpTo_728 : ∀ i, i < 373248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 372736
  · exact minUpTo_727 i h
  have hk := mBlock728 (i - 372736) (by omega)
  rwa [show 372736 + (i - 372736) = i by omega] at hk

theorem minUpTo_729 : ∀ i, i < 373760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 373248
  · exact minUpTo_728 i h
  have hk := mBlock729 (i - 373248) (by omega)
  rwa [show 373248 + (i - 373248) = i by omega] at hk

theorem minUpTo_730 : ∀ i, i < 374272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 373760
  · exact minUpTo_729 i h
  have hk := mBlock730 (i - 373760) (by omega)
  rwa [show 373760 + (i - 373760) = i by omega] at hk

theorem minUpTo_731 : ∀ i, i < 374784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 374272
  · exact minUpTo_730 i h
  have hk := mBlock731 (i - 374272) (by omega)
  rwa [show 374272 + (i - 374272) = i by omega] at hk

theorem minUpTo_732 : ∀ i, i < 375296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 374784
  · exact minUpTo_731 i h
  have hk := mBlock732 (i - 374784) (by omega)
  rwa [show 374784 + (i - 374784) = i by omega] at hk

theorem minUpTo_733 : ∀ i, i < 375808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 375296
  · exact minUpTo_732 i h
  have hk := mBlock733 (i - 375296) (by omega)
  rwa [show 375296 + (i - 375296) = i by omega] at hk

theorem minUpTo_734 : ∀ i, i < 376320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 375808
  · exact minUpTo_733 i h
  have hk := mBlock734 (i - 375808) (by omega)
  rwa [show 375808 + (i - 375808) = i by omega] at hk

theorem minUpTo_735 : ∀ i, i < 376832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 376320
  · exact minUpTo_734 i h
  have hk := mBlock735 (i - 376320) (by omega)
  rwa [show 376320 + (i - 376320) = i by omega] at hk

theorem minUpTo_736 : ∀ i, i < 377344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 376832
  · exact minUpTo_735 i h
  have hk := mBlock736 (i - 376832) (by omega)
  rwa [show 376832 + (i - 376832) = i by omega] at hk

theorem minUpTo_737 : ∀ i, i < 377856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 377344
  · exact minUpTo_736 i h
  have hk := mBlock737 (i - 377344) (by omega)
  rwa [show 377344 + (i - 377344) = i by omega] at hk

theorem minUpTo_738 : ∀ i, i < 378368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 377856
  · exact minUpTo_737 i h
  have hk := mBlock738 (i - 377856) (by omega)
  rwa [show 377856 + (i - 377856) = i by omega] at hk

theorem minUpTo_739 : ∀ i, i < 378880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 378368
  · exact minUpTo_738 i h
  have hk := mBlock739 (i - 378368) (by omega)
  rwa [show 378368 + (i - 378368) = i by omega] at hk

theorem minUpTo_740 : ∀ i, i < 379392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 378880
  · exact minUpTo_739 i h
  have hk := mBlock740 (i - 378880) (by omega)
  rwa [show 378880 + (i - 378880) = i by omega] at hk

theorem minUpTo_741 : ∀ i, i < 379904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 379392
  · exact minUpTo_740 i h
  have hk := mBlock741 (i - 379392) (by omega)
  rwa [show 379392 + (i - 379392) = i by omega] at hk

theorem minUpTo_742 : ∀ i, i < 380416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 379904
  · exact minUpTo_741 i h
  have hk := mBlock742 (i - 379904) (by omega)
  rwa [show 379904 + (i - 379904) = i by omega] at hk

theorem minUpTo_743 : ∀ i, i < 380928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 380416
  · exact minUpTo_742 i h
  have hk := mBlock743 (i - 380416) (by omega)
  rwa [show 380416 + (i - 380416) = i by omega] at hk

theorem minUpTo_744 : ∀ i, i < 381440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 380928
  · exact minUpTo_743 i h
  have hk := mBlock744 (i - 380928) (by omega)
  rwa [show 380928 + (i - 380928) = i by omega] at hk

theorem minUpTo_745 : ∀ i, i < 381952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 381440
  · exact minUpTo_744 i h
  have hk := mBlock745 (i - 381440) (by omega)
  rwa [show 381440 + (i - 381440) = i by omega] at hk

theorem minUpTo_746 : ∀ i, i < 382464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 381952
  · exact minUpTo_745 i h
  have hk := mBlock746 (i - 381952) (by omega)
  rwa [show 381952 + (i - 381952) = i by omega] at hk

theorem minUpTo_747 : ∀ i, i < 382976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 382464
  · exact minUpTo_746 i h
  have hk := mBlock747 (i - 382464) (by omega)
  rwa [show 382464 + (i - 382464) = i by omega] at hk

theorem minUpTo_748 : ∀ i, i < 383488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 382976
  · exact minUpTo_747 i h
  have hk := mBlock748 (i - 382976) (by omega)
  rwa [show 382976 + (i - 382976) = i by omega] at hk

theorem minUpTo_749 : ∀ i, i < 384000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 383488
  · exact minUpTo_748 i h
  have hk := mBlock749 (i - 383488) (by omega)
  rwa [show 383488 + (i - 383488) = i by omega] at hk

theorem minUpTo_750 : ∀ i, i < 384512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 384000
  · exact minUpTo_749 i h
  have hk := mBlock750 (i - 384000) (by omega)
  rwa [show 384000 + (i - 384000) = i by omega] at hk

theorem minUpTo_751 : ∀ i, i < 385024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 384512
  · exact minUpTo_750 i h
  have hk := mBlock751 (i - 384512) (by omega)
  rwa [show 384512 + (i - 384512) = i by omega] at hk

theorem minUpTo_752 : ∀ i, i < 385536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 385024
  · exact minUpTo_751 i h
  have hk := mBlock752 (i - 385024) (by omega)
  rwa [show 385024 + (i - 385024) = i by omega] at hk

theorem minUpTo_753 : ∀ i, i < 386048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 385536
  · exact minUpTo_752 i h
  have hk := mBlock753 (i - 385536) (by omega)
  rwa [show 385536 + (i - 385536) = i by omega] at hk

theorem minUpTo_754 : ∀ i, i < 386560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 386048
  · exact minUpTo_753 i h
  have hk := mBlock754 (i - 386048) (by omega)
  rwa [show 386048 + (i - 386048) = i by omega] at hk

theorem minUpTo_755 : ∀ i, i < 387072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 386560
  · exact minUpTo_754 i h
  have hk := mBlock755 (i - 386560) (by omega)
  rwa [show 386560 + (i - 386560) = i by omega] at hk

theorem minUpTo_756 : ∀ i, i < 387584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 387072
  · exact minUpTo_755 i h
  have hk := mBlock756 (i - 387072) (by omega)
  rwa [show 387072 + (i - 387072) = i by omega] at hk

theorem minUpTo_757 : ∀ i, i < 388096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 387584
  · exact minUpTo_756 i h
  have hk := mBlock757 (i - 387584) (by omega)
  rwa [show 387584 + (i - 387584) = i by omega] at hk

theorem minUpTo_758 : ∀ i, i < 388608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 388096
  · exact minUpTo_757 i h
  have hk := mBlock758 (i - 388096) (by omega)
  rwa [show 388096 + (i - 388096) = i by omega] at hk

theorem minUpTo_759 : ∀ i, i < 389120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 388608
  · exact minUpTo_758 i h
  have hk := mBlock759 (i - 388608) (by omega)
  rwa [show 388608 + (i - 388608) = i by omega] at hk

theorem minUpTo_760 : ∀ i, i < 389632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 389120
  · exact minUpTo_759 i h
  have hk := mBlock760 (i - 389120) (by omega)
  rwa [show 389120 + (i - 389120) = i by omega] at hk

theorem minUpTo_761 : ∀ i, i < 390144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 389632
  · exact minUpTo_760 i h
  have hk := mBlock761 (i - 389632) (by omega)
  rwa [show 389632 + (i - 389632) = i by omega] at hk

theorem minUpTo_762 : ∀ i, i < 390656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 390144
  · exact minUpTo_761 i h
  have hk := mBlock762 (i - 390144) (by omega)
  rwa [show 390144 + (i - 390144) = i by omega] at hk

theorem minUpTo_763 : ∀ i, i < 391168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 390656
  · exact minUpTo_762 i h
  have hk := mBlock763 (i - 390656) (by omega)
  rwa [show 390656 + (i - 390656) = i by omega] at hk

theorem minUpTo_764 : ∀ i, i < 391680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 391168
  · exact minUpTo_763 i h
  have hk := mBlock764 (i - 391168) (by omega)
  rwa [show 391168 + (i - 391168) = i by omega] at hk

theorem minUpTo_765 : ∀ i, i < 392192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 391680
  · exact minUpTo_764 i h
  have hk := mBlock765 (i - 391680) (by omega)
  rwa [show 391680 + (i - 391680) = i by omega] at hk

theorem minUpTo_766 : ∀ i, i < 392704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 392192
  · exact minUpTo_765 i h
  have hk := mBlock766 (i - 392192) (by omega)
  rwa [show 392192 + (i - 392192) = i by omega] at hk

theorem minUpTo_767 : ∀ i, i < 393216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 392704
  · exact minUpTo_766 i h
  have hk := mBlock767 (i - 392704) (by omega)
  rwa [show 392704 + (i - 392704) = i by omega] at hk

theorem minUpTo_768 : ∀ i, i < 393728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 393216
  · exact minUpTo_767 i h
  have hk := mBlock768 (i - 393216) (by omega)
  rwa [show 393216 + (i - 393216) = i by omega] at hk

theorem minUpTo_769 : ∀ i, i < 394240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 393728
  · exact minUpTo_768 i h
  have hk := mBlock769 (i - 393728) (by omega)
  rwa [show 393728 + (i - 393728) = i by omega] at hk

theorem minUpTo_770 : ∀ i, i < 394752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 394240
  · exact minUpTo_769 i h
  have hk := mBlock770 (i - 394240) (by omega)
  rwa [show 394240 + (i - 394240) = i by omega] at hk

theorem minUpTo_771 : ∀ i, i < 395264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 394752
  · exact minUpTo_770 i h
  have hk := mBlock771 (i - 394752) (by omega)
  rwa [show 394752 + (i - 394752) = i by omega] at hk

theorem minUpTo_772 : ∀ i, i < 395776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 395264
  · exact minUpTo_771 i h
  have hk := mBlock772 (i - 395264) (by omega)
  rwa [show 395264 + (i - 395264) = i by omega] at hk

theorem minUpTo_773 : ∀ i, i < 396288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 395776
  · exact minUpTo_772 i h
  have hk := mBlock773 (i - 395776) (by omega)
  rwa [show 395776 + (i - 395776) = i by omega] at hk

theorem minUpTo_774 : ∀ i, i < 396800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 396288
  · exact minUpTo_773 i h
  have hk := mBlock774 (i - 396288) (by omega)
  rwa [show 396288 + (i - 396288) = i by omega] at hk

theorem minUpTo_775 : ∀ i, i < 397312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 396800
  · exact minUpTo_774 i h
  have hk := mBlock775 (i - 396800) (by omega)
  rwa [show 396800 + (i - 396800) = i by omega] at hk

theorem minUpTo_776 : ∀ i, i < 397824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 397312
  · exact minUpTo_775 i h
  have hk := mBlock776 (i - 397312) (by omega)
  rwa [show 397312 + (i - 397312) = i by omega] at hk

theorem minUpTo_777 : ∀ i, i < 398336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 397824
  · exact minUpTo_776 i h
  have hk := mBlock777 (i - 397824) (by omega)
  rwa [show 397824 + (i - 397824) = i by omega] at hk

theorem minUpTo_778 : ∀ i, i < 398848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 398336
  · exact minUpTo_777 i h
  have hk := mBlock778 (i - 398336) (by omega)
  rwa [show 398336 + (i - 398336) = i by omega] at hk

theorem minUpTo_779 : ∀ i, i < 399360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 398848
  · exact minUpTo_778 i h
  have hk := mBlock779 (i - 398848) (by omega)
  rwa [show 398848 + (i - 398848) = i by omega] at hk

theorem minUpTo_780 : ∀ i, i < 399872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 399360
  · exact minUpTo_779 i h
  have hk := mBlock780 (i - 399360) (by omega)
  rwa [show 399360 + (i - 399360) = i by omega] at hk

theorem minUpTo_781 : ∀ i, i < 400384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 399872
  · exact minUpTo_780 i h
  have hk := mBlock781 (i - 399872) (by omega)
  rwa [show 399872 + (i - 399872) = i by omega] at hk

theorem minUpTo_782 : ∀ i, i < 400896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 400384
  · exact minUpTo_781 i h
  have hk := mBlock782 (i - 400384) (by omega)
  rwa [show 400384 + (i - 400384) = i by omega] at hk

theorem minUpTo_783 : ∀ i, i < 401408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 400896
  · exact minUpTo_782 i h
  have hk := mBlock783 (i - 400896) (by omega)
  rwa [show 400896 + (i - 400896) = i by omega] at hk

theorem minUpTo_784 : ∀ i, i < 401920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 401408
  · exact minUpTo_783 i h
  have hk := mBlock784 (i - 401408) (by omega)
  rwa [show 401408 + (i - 401408) = i by omega] at hk

theorem minUpTo_785 : ∀ i, i < 402432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 401920
  · exact minUpTo_784 i h
  have hk := mBlock785 (i - 401920) (by omega)
  rwa [show 401920 + (i - 401920) = i by omega] at hk

theorem minUpTo_786 : ∀ i, i < 402944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 402432
  · exact minUpTo_785 i h
  have hk := mBlock786 (i - 402432) (by omega)
  rwa [show 402432 + (i - 402432) = i by omega] at hk

theorem minUpTo_787 : ∀ i, i < 403456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 402944
  · exact minUpTo_786 i h
  have hk := mBlock787 (i - 402944) (by omega)
  rwa [show 402944 + (i - 402944) = i by omega] at hk

theorem minUpTo_788 : ∀ i, i < 403968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 403456
  · exact minUpTo_787 i h
  have hk := mBlock788 (i - 403456) (by omega)
  rwa [show 403456 + (i - 403456) = i by omega] at hk

theorem minUpTo_789 : ∀ i, i < 404480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 403968
  · exact minUpTo_788 i h
  have hk := mBlock789 (i - 403968) (by omega)
  rwa [show 403968 + (i - 403968) = i by omega] at hk

theorem minUpTo_790 : ∀ i, i < 404992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 404480
  · exact minUpTo_789 i h
  have hk := mBlock790 (i - 404480) (by omega)
  rwa [show 404480 + (i - 404480) = i by omega] at hk

theorem minUpTo_791 : ∀ i, i < 405504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 404992
  · exact minUpTo_790 i h
  have hk := mBlock791 (i - 404992) (by omega)
  rwa [show 404992 + (i - 404992) = i by omega] at hk

theorem minUpTo_792 : ∀ i, i < 406016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 405504
  · exact minUpTo_791 i h
  have hk := mBlock792 (i - 405504) (by omega)
  rwa [show 405504 + (i - 405504) = i by omega] at hk

theorem minUpTo_793 : ∀ i, i < 406528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 406016
  · exact minUpTo_792 i h
  have hk := mBlock793 (i - 406016) (by omega)
  rwa [show 406016 + (i - 406016) = i by omega] at hk

theorem minUpTo_794 : ∀ i, i < 407040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 406528
  · exact minUpTo_793 i h
  have hk := mBlock794 (i - 406528) (by omega)
  rwa [show 406528 + (i - 406528) = i by omega] at hk

theorem minUpTo_795 : ∀ i, i < 407552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 407040
  · exact minUpTo_794 i h
  have hk := mBlock795 (i - 407040) (by omega)
  rwa [show 407040 + (i - 407040) = i by omega] at hk

theorem minUpTo_796 : ∀ i, i < 408064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 407552
  · exact minUpTo_795 i h
  have hk := mBlock796 (i - 407552) (by omega)
  rwa [show 407552 + (i - 407552) = i by omega] at hk

theorem minUpTo_797 : ∀ i, i < 408576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 408064
  · exact minUpTo_796 i h
  have hk := mBlock797 (i - 408064) (by omega)
  rwa [show 408064 + (i - 408064) = i by omega] at hk

theorem minUpTo_798 : ∀ i, i < 409088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 408576
  · exact minUpTo_797 i h
  have hk := mBlock798 (i - 408576) (by omega)
  rwa [show 408576 + (i - 408576) = i by omega] at hk

theorem minUpTo_799 : ∀ i, i < 409600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 409088
  · exact minUpTo_798 i h
  have hk := mBlock799 (i - 409088) (by omega)
  rwa [show 409088 + (i - 409088) = i by omega] at hk

theorem minUpTo_800 : ∀ i, i < 410112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 409600
  · exact minUpTo_799 i h
  have hk := mBlock800 (i - 409600) (by omega)
  rwa [show 409600 + (i - 409600) = i by omega] at hk

theorem minUpTo_801 : ∀ i, i < 410624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 410112
  · exact minUpTo_800 i h
  have hk := mBlock801 (i - 410112) (by omega)
  rwa [show 410112 + (i - 410112) = i by omega] at hk

theorem minUpTo_802 : ∀ i, i < 411136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 410624
  · exact minUpTo_801 i h
  have hk := mBlock802 (i - 410624) (by omega)
  rwa [show 410624 + (i - 410624) = i by omega] at hk

theorem minUpTo_803 : ∀ i, i < 411648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 411136
  · exact minUpTo_802 i h
  have hk := mBlock803 (i - 411136) (by omega)
  rwa [show 411136 + (i - 411136) = i by omega] at hk

theorem minUpTo_804 : ∀ i, i < 412160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 411648
  · exact minUpTo_803 i h
  have hk := mBlock804 (i - 411648) (by omega)
  rwa [show 411648 + (i - 411648) = i by omega] at hk

theorem minUpTo_805 : ∀ i, i < 412672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 412160
  · exact minUpTo_804 i h
  have hk := mBlock805 (i - 412160) (by omega)
  rwa [show 412160 + (i - 412160) = i by omega] at hk

theorem minUpTo_806 : ∀ i, i < 413184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 412672
  · exact minUpTo_805 i h
  have hk := mBlock806 (i - 412672) (by omega)
  rwa [show 412672 + (i - 412672) = i by omega] at hk

theorem minUpTo_807 : ∀ i, i < 413696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 413184
  · exact minUpTo_806 i h
  have hk := mBlock807 (i - 413184) (by omega)
  rwa [show 413184 + (i - 413184) = i by omega] at hk

theorem minUpTo_808 : ∀ i, i < 414208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 413696
  · exact minUpTo_807 i h
  have hk := mBlock808 (i - 413696) (by omega)
  rwa [show 413696 + (i - 413696) = i by omega] at hk

theorem minUpTo_809 : ∀ i, i < 414720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 414208
  · exact minUpTo_808 i h
  have hk := mBlock809 (i - 414208) (by omega)
  rwa [show 414208 + (i - 414208) = i by omega] at hk

theorem minUpTo_810 : ∀ i, i < 415232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 414720
  · exact minUpTo_809 i h
  have hk := mBlock810 (i - 414720) (by omega)
  rwa [show 414720 + (i - 414720) = i by omega] at hk

theorem minUpTo_811 : ∀ i, i < 415744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 415232
  · exact minUpTo_810 i h
  have hk := mBlock811 (i - 415232) (by omega)
  rwa [show 415232 + (i - 415232) = i by omega] at hk

theorem minUpTo_812 : ∀ i, i < 416256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 415744
  · exact minUpTo_811 i h
  have hk := mBlock812 (i - 415744) (by omega)
  rwa [show 415744 + (i - 415744) = i by omega] at hk

theorem minUpTo_813 : ∀ i, i < 416768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 416256
  · exact minUpTo_812 i h
  have hk := mBlock813 (i - 416256) (by omega)
  rwa [show 416256 + (i - 416256) = i by omega] at hk

theorem minUpTo_814 : ∀ i, i < 417280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 416768
  · exact minUpTo_813 i h
  have hk := mBlock814 (i - 416768) (by omega)
  rwa [show 416768 + (i - 416768) = i by omega] at hk

theorem minUpTo_815 : ∀ i, i < 417792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 417280
  · exact minUpTo_814 i h
  have hk := mBlock815 (i - 417280) (by omega)
  rwa [show 417280 + (i - 417280) = i by omega] at hk

theorem minUpTo_816 : ∀ i, i < 418304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 417792
  · exact minUpTo_815 i h
  have hk := mBlock816 (i - 417792) (by omega)
  rwa [show 417792 + (i - 417792) = i by omega] at hk

theorem minUpTo_817 : ∀ i, i < 418816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 418304
  · exact minUpTo_816 i h
  have hk := mBlock817 (i - 418304) (by omega)
  rwa [show 418304 + (i - 418304) = i by omega] at hk

theorem minUpTo_818 : ∀ i, i < 419328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 418816
  · exact minUpTo_817 i h
  have hk := mBlock818 (i - 418816) (by omega)
  rwa [show 418816 + (i - 418816) = i by omega] at hk

theorem minUpTo_819 : ∀ i, i < 419840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 419328
  · exact minUpTo_818 i h
  have hk := mBlock819 (i - 419328) (by omega)
  rwa [show 419328 + (i - 419328) = i by omega] at hk

theorem minUpTo_820 : ∀ i, i < 420352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 419840
  · exact minUpTo_819 i h
  have hk := mBlock820 (i - 419840) (by omega)
  rwa [show 419840 + (i - 419840) = i by omega] at hk

theorem minUpTo_821 : ∀ i, i < 420864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 420352
  · exact minUpTo_820 i h
  have hk := mBlock821 (i - 420352) (by omega)
  rwa [show 420352 + (i - 420352) = i by omega] at hk

theorem minUpTo_822 : ∀ i, i < 421376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 420864
  · exact minUpTo_821 i h
  have hk := mBlock822 (i - 420864) (by omega)
  rwa [show 420864 + (i - 420864) = i by omega] at hk

theorem minUpTo_823 : ∀ i, i < 421888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 421376
  · exact minUpTo_822 i h
  have hk := mBlock823 (i - 421376) (by omega)
  rwa [show 421376 + (i - 421376) = i by omega] at hk

theorem minUpTo_824 : ∀ i, i < 422400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 421888
  · exact minUpTo_823 i h
  have hk := mBlock824 (i - 421888) (by omega)
  rwa [show 421888 + (i - 421888) = i by omega] at hk

theorem minUpTo_825 : ∀ i, i < 422912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 422400
  · exact minUpTo_824 i h
  have hk := mBlock825 (i - 422400) (by omega)
  rwa [show 422400 + (i - 422400) = i by omega] at hk

theorem minUpTo_826 : ∀ i, i < 423424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 422912
  · exact minUpTo_825 i h
  have hk := mBlock826 (i - 422912) (by omega)
  rwa [show 422912 + (i - 422912) = i by omega] at hk

theorem minUpTo_827 : ∀ i, i < 423936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 423424
  · exact minUpTo_826 i h
  have hk := mBlock827 (i - 423424) (by omega)
  rwa [show 423424 + (i - 423424) = i by omega] at hk

theorem minUpTo_828 : ∀ i, i < 424448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 423936
  · exact minUpTo_827 i h
  have hk := mBlock828 (i - 423936) (by omega)
  rwa [show 423936 + (i - 423936) = i by omega] at hk

theorem minUpTo_829 : ∀ i, i < 424960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 424448
  · exact minUpTo_828 i h
  have hk := mBlock829 (i - 424448) (by omega)
  rwa [show 424448 + (i - 424448) = i by omega] at hk

theorem minUpTo_830 : ∀ i, i < 425472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 424960
  · exact minUpTo_829 i h
  have hk := mBlock830 (i - 424960) (by omega)
  rwa [show 424960 + (i - 424960) = i by omega] at hk

theorem minUpTo_831 : ∀ i, i < 425984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 425472
  · exact minUpTo_830 i h
  have hk := mBlock831 (i - 425472) (by omega)
  rwa [show 425472 + (i - 425472) = i by omega] at hk

theorem minUpTo_832 : ∀ i, i < 426496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 425984
  · exact minUpTo_831 i h
  have hk := mBlock832 (i - 425984) (by omega)
  rwa [show 425984 + (i - 425984) = i by omega] at hk

theorem minUpTo_833 : ∀ i, i < 427008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 426496
  · exact minUpTo_832 i h
  have hk := mBlock833 (i - 426496) (by omega)
  rwa [show 426496 + (i - 426496) = i by omega] at hk

theorem minUpTo_834 : ∀ i, i < 427520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 427008
  · exact minUpTo_833 i h
  have hk := mBlock834 (i - 427008) (by omega)
  rwa [show 427008 + (i - 427008) = i by omega] at hk

theorem minUpTo_835 : ∀ i, i < 428032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 427520
  · exact minUpTo_834 i h
  have hk := mBlock835 (i - 427520) (by omega)
  rwa [show 427520 + (i - 427520) = i by omega] at hk

theorem minUpTo_836 : ∀ i, i < 428544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 428032
  · exact minUpTo_835 i h
  have hk := mBlock836 (i - 428032) (by omega)
  rwa [show 428032 + (i - 428032) = i by omega] at hk

theorem minUpTo_837 : ∀ i, i < 429056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 428544
  · exact minUpTo_836 i h
  have hk := mBlock837 (i - 428544) (by omega)
  rwa [show 428544 + (i - 428544) = i by omega] at hk

theorem minUpTo_838 : ∀ i, i < 429568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 429056
  · exact minUpTo_837 i h
  have hk := mBlock838 (i - 429056) (by omega)
  rwa [show 429056 + (i - 429056) = i by omega] at hk

theorem minUpTo_839 : ∀ i, i < 430080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 429568
  · exact minUpTo_838 i h
  have hk := mBlock839 (i - 429568) (by omega)
  rwa [show 429568 + (i - 429568) = i by omega] at hk

theorem minUpTo_840 : ∀ i, i < 430592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 430080
  · exact minUpTo_839 i h
  have hk := mBlock840 (i - 430080) (by omega)
  rwa [show 430080 + (i - 430080) = i by omega] at hk

theorem minUpTo_841 : ∀ i, i < 431104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 430592
  · exact minUpTo_840 i h
  have hk := mBlock841 (i - 430592) (by omega)
  rwa [show 430592 + (i - 430592) = i by omega] at hk

theorem minUpTo_842 : ∀ i, i < 431616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 431104
  · exact minUpTo_841 i h
  have hk := mBlock842 (i - 431104) (by omega)
  rwa [show 431104 + (i - 431104) = i by omega] at hk

theorem minUpTo_843 : ∀ i, i < 432128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 431616
  · exact minUpTo_842 i h
  have hk := mBlock843 (i - 431616) (by omega)
  rwa [show 431616 + (i - 431616) = i by omega] at hk

theorem minUpTo_844 : ∀ i, i < 432640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 432128
  · exact minUpTo_843 i h
  have hk := mBlock844 (i - 432128) (by omega)
  rwa [show 432128 + (i - 432128) = i by omega] at hk

theorem minUpTo_845 : ∀ i, i < 433152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 432640
  · exact minUpTo_844 i h
  have hk := mBlock845 (i - 432640) (by omega)
  rwa [show 432640 + (i - 432640) = i by omega] at hk

theorem minUpTo_846 : ∀ i, i < 433664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 433152
  · exact minUpTo_845 i h
  have hk := mBlock846 (i - 433152) (by omega)
  rwa [show 433152 + (i - 433152) = i by omega] at hk

theorem minUpTo_847 : ∀ i, i < 434176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 433664
  · exact minUpTo_846 i h
  have hk := mBlock847 (i - 433664) (by omega)
  rwa [show 433664 + (i - 433664) = i by omega] at hk

theorem minUpTo_848 : ∀ i, i < 434688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 434176
  · exact minUpTo_847 i h
  have hk := mBlock848 (i - 434176) (by omega)
  rwa [show 434176 + (i - 434176) = i by omega] at hk

theorem minUpTo_849 : ∀ i, i < 435200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 434688
  · exact minUpTo_848 i h
  have hk := mBlock849 (i - 434688) (by omega)
  rwa [show 434688 + (i - 434688) = i by omega] at hk

theorem minUpTo_850 : ∀ i, i < 435712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 435200
  · exact minUpTo_849 i h
  have hk := mBlock850 (i - 435200) (by omega)
  rwa [show 435200 + (i - 435200) = i by omega] at hk

theorem minUpTo_851 : ∀ i, i < 436224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 435712
  · exact minUpTo_850 i h
  have hk := mBlock851 (i - 435712) (by omega)
  rwa [show 435712 + (i - 435712) = i by omega] at hk

theorem minUpTo_852 : ∀ i, i < 436736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 436224
  · exact minUpTo_851 i h
  have hk := mBlock852 (i - 436224) (by omega)
  rwa [show 436224 + (i - 436224) = i by omega] at hk

theorem minUpTo_853 : ∀ i, i < 437248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 436736
  · exact minUpTo_852 i h
  have hk := mBlock853 (i - 436736) (by omega)
  rwa [show 436736 + (i - 436736) = i by omega] at hk

theorem minUpTo_854 : ∀ i, i < 437760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 437248
  · exact minUpTo_853 i h
  have hk := mBlock854 (i - 437248) (by omega)
  rwa [show 437248 + (i - 437248) = i by omega] at hk

theorem minUpTo_855 : ∀ i, i < 438272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 437760
  · exact minUpTo_854 i h
  have hk := mBlock855 (i - 437760) (by omega)
  rwa [show 437760 + (i - 437760) = i by omega] at hk

theorem minUpTo_856 : ∀ i, i < 438784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 438272
  · exact minUpTo_855 i h
  have hk := mBlock856 (i - 438272) (by omega)
  rwa [show 438272 + (i - 438272) = i by omega] at hk

theorem minUpTo_857 : ∀ i, i < 439296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 438784
  · exact minUpTo_856 i h
  have hk := mBlock857 (i - 438784) (by omega)
  rwa [show 438784 + (i - 438784) = i by omega] at hk

theorem minUpTo_858 : ∀ i, i < 439808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 439296
  · exact minUpTo_857 i h
  have hk := mBlock858 (i - 439296) (by omega)
  rwa [show 439296 + (i - 439296) = i by omega] at hk

theorem minUpTo_859 : ∀ i, i < 440320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 439808
  · exact minUpTo_858 i h
  have hk := mBlock859 (i - 439808) (by omega)
  rwa [show 439808 + (i - 439808) = i by omega] at hk

theorem minUpTo_860 : ∀ i, i < 440832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 440320
  · exact minUpTo_859 i h
  have hk := mBlock860 (i - 440320) (by omega)
  rwa [show 440320 + (i - 440320) = i by omega] at hk

theorem minUpTo_861 : ∀ i, i < 441344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 440832
  · exact minUpTo_860 i h
  have hk := mBlock861 (i - 440832) (by omega)
  rwa [show 440832 + (i - 440832) = i by omega] at hk

theorem minUpTo_862 : ∀ i, i < 441856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 441344
  · exact minUpTo_861 i h
  have hk := mBlock862 (i - 441344) (by omega)
  rwa [show 441344 + (i - 441344) = i by omega] at hk

theorem minUpTo_863 : ∀ i, i < 442368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 441856
  · exact minUpTo_862 i h
  have hk := mBlock863 (i - 441856) (by omega)
  rwa [show 441856 + (i - 441856) = i by omega] at hk

theorem minUpTo_864 : ∀ i, i < 442880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 442368
  · exact minUpTo_863 i h
  have hk := mBlock864 (i - 442368) (by omega)
  rwa [show 442368 + (i - 442368) = i by omega] at hk

theorem minUpTo_865 : ∀ i, i < 443392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 442880
  · exact minUpTo_864 i h
  have hk := mBlock865 (i - 442880) (by omega)
  rwa [show 442880 + (i - 442880) = i by omega] at hk

theorem minUpTo_866 : ∀ i, i < 443904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 443392
  · exact minUpTo_865 i h
  have hk := mBlock866 (i - 443392) (by omega)
  rwa [show 443392 + (i - 443392) = i by omega] at hk

theorem minUpTo_867 : ∀ i, i < 444416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 443904
  · exact minUpTo_866 i h
  have hk := mBlock867 (i - 443904) (by omega)
  rwa [show 443904 + (i - 443904) = i by omega] at hk

theorem minUpTo_868 : ∀ i, i < 444928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 444416
  · exact minUpTo_867 i h
  have hk := mBlock868 (i - 444416) (by omega)
  rwa [show 444416 + (i - 444416) = i by omega] at hk

theorem minUpTo_869 : ∀ i, i < 445440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 444928
  · exact minUpTo_868 i h
  have hk := mBlock869 (i - 444928) (by omega)
  rwa [show 444928 + (i - 444928) = i by omega] at hk

theorem minUpTo_870 : ∀ i, i < 445952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 445440
  · exact minUpTo_869 i h
  have hk := mBlock870 (i - 445440) (by omega)
  rwa [show 445440 + (i - 445440) = i by omega] at hk

theorem minUpTo_871 : ∀ i, i < 446464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 445952
  · exact minUpTo_870 i h
  have hk := mBlock871 (i - 445952) (by omega)
  rwa [show 445952 + (i - 445952) = i by omega] at hk

theorem minUpTo_872 : ∀ i, i < 446976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 446464
  · exact minUpTo_871 i h
  have hk := mBlock872 (i - 446464) (by omega)
  rwa [show 446464 + (i - 446464) = i by omega] at hk

theorem minUpTo_873 : ∀ i, i < 447488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 446976
  · exact minUpTo_872 i h
  have hk := mBlock873 (i - 446976) (by omega)
  rwa [show 446976 + (i - 446976) = i by omega] at hk

theorem minUpTo_874 : ∀ i, i < 448000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 447488
  · exact minUpTo_873 i h
  have hk := mBlock874 (i - 447488) (by omega)
  rwa [show 447488 + (i - 447488) = i by omega] at hk

theorem minUpTo_875 : ∀ i, i < 448512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 448000
  · exact minUpTo_874 i h
  have hk := mBlock875 (i - 448000) (by omega)
  rwa [show 448000 + (i - 448000) = i by omega] at hk

theorem minUpTo_876 : ∀ i, i < 449024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 448512
  · exact minUpTo_875 i h
  have hk := mBlock876 (i - 448512) (by omega)
  rwa [show 448512 + (i - 448512) = i by omega] at hk

theorem minUpTo_877 : ∀ i, i < 449536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 449024
  · exact minUpTo_876 i h
  have hk := mBlock877 (i - 449024) (by omega)
  rwa [show 449024 + (i - 449024) = i by omega] at hk

theorem minUpTo_878 : ∀ i, i < 450048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 449536
  · exact minUpTo_877 i h
  have hk := mBlock878 (i - 449536) (by omega)
  rwa [show 449536 + (i - 449536) = i by omega] at hk

theorem minUpTo_879 : ∀ i, i < 450560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 450048
  · exact minUpTo_878 i h
  have hk := mBlock879 (i - 450048) (by omega)
  rwa [show 450048 + (i - 450048) = i by omega] at hk

theorem minUpTo_880 : ∀ i, i < 451072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 450560
  · exact minUpTo_879 i h
  have hk := mBlock880 (i - 450560) (by omega)
  rwa [show 450560 + (i - 450560) = i by omega] at hk

theorem minUpTo_881 : ∀ i, i < 451584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 451072
  · exact minUpTo_880 i h
  have hk := mBlock881 (i - 451072) (by omega)
  rwa [show 451072 + (i - 451072) = i by omega] at hk

theorem minUpTo_882 : ∀ i, i < 452096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 451584
  · exact minUpTo_881 i h
  have hk := mBlock882 (i - 451584) (by omega)
  rwa [show 451584 + (i - 451584) = i by omega] at hk

theorem minUpTo_883 : ∀ i, i < 452608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 452096
  · exact minUpTo_882 i h
  have hk := mBlock883 (i - 452096) (by omega)
  rwa [show 452096 + (i - 452096) = i by omega] at hk

theorem minUpTo_884 : ∀ i, i < 453120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 452608
  · exact minUpTo_883 i h
  have hk := mBlock884 (i - 452608) (by omega)
  rwa [show 452608 + (i - 452608) = i by omega] at hk

theorem minUpTo_885 : ∀ i, i < 453632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 453120
  · exact minUpTo_884 i h
  have hk := mBlock885 (i - 453120) (by omega)
  rwa [show 453120 + (i - 453120) = i by omega] at hk

theorem minUpTo_886 : ∀ i, i < 454144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 453632
  · exact minUpTo_885 i h
  have hk := mBlock886 (i - 453632) (by omega)
  rwa [show 453632 + (i - 453632) = i by omega] at hk

theorem minUpTo_887 : ∀ i, i < 454656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 454144
  · exact minUpTo_886 i h
  have hk := mBlock887 (i - 454144) (by omega)
  rwa [show 454144 + (i - 454144) = i by omega] at hk

theorem minUpTo_888 : ∀ i, i < 455168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 454656
  · exact minUpTo_887 i h
  have hk := mBlock888 (i - 454656) (by omega)
  rwa [show 454656 + (i - 454656) = i by omega] at hk

theorem minUpTo_889 : ∀ i, i < 455680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 455168
  · exact minUpTo_888 i h
  have hk := mBlock889 (i - 455168) (by omega)
  rwa [show 455168 + (i - 455168) = i by omega] at hk

theorem minUpTo_890 : ∀ i, i < 456192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 455680
  · exact minUpTo_889 i h
  have hk := mBlock890 (i - 455680) (by omega)
  rwa [show 455680 + (i - 455680) = i by omega] at hk

theorem minUpTo_891 : ∀ i, i < 456704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 456192
  · exact minUpTo_890 i h
  have hk := mBlock891 (i - 456192) (by omega)
  rwa [show 456192 + (i - 456192) = i by omega] at hk

theorem minUpTo_892 : ∀ i, i < 457216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 456704
  · exact minUpTo_891 i h
  have hk := mBlock892 (i - 456704) (by omega)
  rwa [show 456704 + (i - 456704) = i by omega] at hk

theorem minUpTo_893 : ∀ i, i < 457728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 457216
  · exact minUpTo_892 i h
  have hk := mBlock893 (i - 457216) (by omega)
  rwa [show 457216 + (i - 457216) = i by omega] at hk

theorem minUpTo_894 : ∀ i, i < 458240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 457728
  · exact minUpTo_893 i h
  have hk := mBlock894 (i - 457728) (by omega)
  rwa [show 457728 + (i - 457728) = i by omega] at hk

theorem minUpTo_895 : ∀ i, i < 458752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 458240
  · exact minUpTo_894 i h
  have hk := mBlock895 (i - 458240) (by omega)
  rwa [show 458240 + (i - 458240) = i by omega] at hk

theorem minUpTo_896 : ∀ i, i < 459264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 458752
  · exact minUpTo_895 i h
  have hk := mBlock896 (i - 458752) (by omega)
  rwa [show 458752 + (i - 458752) = i by omega] at hk

theorem minUpTo_897 : ∀ i, i < 459776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 459264
  · exact minUpTo_896 i h
  have hk := mBlock897 (i - 459264) (by omega)
  rwa [show 459264 + (i - 459264) = i by omega] at hk

theorem minUpTo_898 : ∀ i, i < 460288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 459776
  · exact minUpTo_897 i h
  have hk := mBlock898 (i - 459776) (by omega)
  rwa [show 459776 + (i - 459776) = i by omega] at hk

theorem minUpTo_899 : ∀ i, i < 460800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 460288
  · exact minUpTo_898 i h
  have hk := mBlock899 (i - 460288) (by omega)
  rwa [show 460288 + (i - 460288) = i by omega] at hk

theorem minUpTo_900 : ∀ i, i < 461312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 460800
  · exact minUpTo_899 i h
  have hk := mBlock900 (i - 460800) (by omega)
  rwa [show 460800 + (i - 460800) = i by omega] at hk

theorem minUpTo_901 : ∀ i, i < 461824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 461312
  · exact minUpTo_900 i h
  have hk := mBlock901 (i - 461312) (by omega)
  rwa [show 461312 + (i - 461312) = i by omega] at hk

theorem minUpTo_902 : ∀ i, i < 462336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 461824
  · exact minUpTo_901 i h
  have hk := mBlock902 (i - 461824) (by omega)
  rwa [show 461824 + (i - 461824) = i by omega] at hk

theorem minUpTo_903 : ∀ i, i < 462848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 462336
  · exact minUpTo_902 i h
  have hk := mBlock903 (i - 462336) (by omega)
  rwa [show 462336 + (i - 462336) = i by omega] at hk

theorem minUpTo_904 : ∀ i, i < 463360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 462848
  · exact minUpTo_903 i h
  have hk := mBlock904 (i - 462848) (by omega)
  rwa [show 462848 + (i - 462848) = i by omega] at hk

theorem minUpTo_905 : ∀ i, i < 463872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 463360
  · exact minUpTo_904 i h
  have hk := mBlock905 (i - 463360) (by omega)
  rwa [show 463360 + (i - 463360) = i by omega] at hk

theorem minUpTo_906 : ∀ i, i < 464384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 463872
  · exact minUpTo_905 i h
  have hk := mBlock906 (i - 463872) (by omega)
  rwa [show 463872 + (i - 463872) = i by omega] at hk

theorem minUpTo_907 : ∀ i, i < 464896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 464384
  · exact minUpTo_906 i h
  have hk := mBlock907 (i - 464384) (by omega)
  rwa [show 464384 + (i - 464384) = i by omega] at hk

theorem minUpTo_908 : ∀ i, i < 465408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 464896
  · exact minUpTo_907 i h
  have hk := mBlock908 (i - 464896) (by omega)
  rwa [show 464896 + (i - 464896) = i by omega] at hk

theorem minUpTo_909 : ∀ i, i < 465920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 465408
  · exact minUpTo_908 i h
  have hk := mBlock909 (i - 465408) (by omega)
  rwa [show 465408 + (i - 465408) = i by omega] at hk

theorem minUpTo_910 : ∀ i, i < 466432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 465920
  · exact minUpTo_909 i h
  have hk := mBlock910 (i - 465920) (by omega)
  rwa [show 465920 + (i - 465920) = i by omega] at hk

theorem minUpTo_911 : ∀ i, i < 466944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 466432
  · exact minUpTo_910 i h
  have hk := mBlock911 (i - 466432) (by omega)
  rwa [show 466432 + (i - 466432) = i by omega] at hk

theorem minUpTo_912 : ∀ i, i < 467456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 466944
  · exact minUpTo_911 i h
  have hk := mBlock912 (i - 466944) (by omega)
  rwa [show 466944 + (i - 466944) = i by omega] at hk

theorem minUpTo_913 : ∀ i, i < 467968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 467456
  · exact minUpTo_912 i h
  have hk := mBlock913 (i - 467456) (by omega)
  rwa [show 467456 + (i - 467456) = i by omega] at hk

theorem minUpTo_914 : ∀ i, i < 468480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 467968
  · exact minUpTo_913 i h
  have hk := mBlock914 (i - 467968) (by omega)
  rwa [show 467968 + (i - 467968) = i by omega] at hk

theorem minUpTo_915 : ∀ i, i < 468992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 468480
  · exact minUpTo_914 i h
  have hk := mBlock915 (i - 468480) (by omega)
  rwa [show 468480 + (i - 468480) = i by omega] at hk

theorem minUpTo_916 : ∀ i, i < 469504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 468992
  · exact minUpTo_915 i h
  have hk := mBlock916 (i - 468992) (by omega)
  rwa [show 468992 + (i - 468992) = i by omega] at hk

theorem minUpTo_917 : ∀ i, i < 470016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 469504
  · exact minUpTo_916 i h
  have hk := mBlock917 (i - 469504) (by omega)
  rwa [show 469504 + (i - 469504) = i by omega] at hk

theorem minUpTo_918 : ∀ i, i < 470528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 470016
  · exact minUpTo_917 i h
  have hk := mBlock918 (i - 470016) (by omega)
  rwa [show 470016 + (i - 470016) = i by omega] at hk

theorem minUpTo_919 : ∀ i, i < 471040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 470528
  · exact minUpTo_918 i h
  have hk := mBlock919 (i - 470528) (by omega)
  rwa [show 470528 + (i - 470528) = i by omega] at hk

theorem minUpTo_920 : ∀ i, i < 471552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 471040
  · exact minUpTo_919 i h
  have hk := mBlock920 (i - 471040) (by omega)
  rwa [show 471040 + (i - 471040) = i by omega] at hk

theorem minUpTo_921 : ∀ i, i < 472064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 471552
  · exact minUpTo_920 i h
  have hk := mBlock921 (i - 471552) (by omega)
  rwa [show 471552 + (i - 471552) = i by omega] at hk

theorem minUpTo_922 : ∀ i, i < 472576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 472064
  · exact minUpTo_921 i h
  have hk := mBlock922 (i - 472064) (by omega)
  rwa [show 472064 + (i - 472064) = i by omega] at hk

theorem minUpTo_923 : ∀ i, i < 473088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 472576
  · exact minUpTo_922 i h
  have hk := mBlock923 (i - 472576) (by omega)
  rwa [show 472576 + (i - 472576) = i by omega] at hk

theorem minUpTo_924 : ∀ i, i < 473600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 473088
  · exact minUpTo_923 i h
  have hk := mBlock924 (i - 473088) (by omega)
  rwa [show 473088 + (i - 473088) = i by omega] at hk

theorem minUpTo_925 : ∀ i, i < 474112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 473600
  · exact minUpTo_924 i h
  have hk := mBlock925 (i - 473600) (by omega)
  rwa [show 473600 + (i - 473600) = i by omega] at hk

theorem minUpTo_926 : ∀ i, i < 474624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 474112
  · exact minUpTo_925 i h
  have hk := mBlock926 (i - 474112) (by omega)
  rwa [show 474112 + (i - 474112) = i by omega] at hk

theorem minUpTo_927 : ∀ i, i < 475136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 474624
  · exact minUpTo_926 i h
  have hk := mBlock927 (i - 474624) (by omega)
  rwa [show 474624 + (i - 474624) = i by omega] at hk

theorem minUpTo_928 : ∀ i, i < 475648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 475136
  · exact minUpTo_927 i h
  have hk := mBlock928 (i - 475136) (by omega)
  rwa [show 475136 + (i - 475136) = i by omega] at hk

theorem minUpTo_929 : ∀ i, i < 476160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 475648
  · exact minUpTo_928 i h
  have hk := mBlock929 (i - 475648) (by omega)
  rwa [show 475648 + (i - 475648) = i by omega] at hk

theorem minUpTo_930 : ∀ i, i < 476672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 476160
  · exact minUpTo_929 i h
  have hk := mBlock930 (i - 476160) (by omega)
  rwa [show 476160 + (i - 476160) = i by omega] at hk

theorem minUpTo_931 : ∀ i, i < 477184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 476672
  · exact minUpTo_930 i h
  have hk := mBlock931 (i - 476672) (by omega)
  rwa [show 476672 + (i - 476672) = i by omega] at hk

theorem minUpTo_932 : ∀ i, i < 477696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 477184
  · exact minUpTo_931 i h
  have hk := mBlock932 (i - 477184) (by omega)
  rwa [show 477184 + (i - 477184) = i by omega] at hk

theorem minUpTo_933 : ∀ i, i < 478208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 477696
  · exact minUpTo_932 i h
  have hk := mBlock933 (i - 477696) (by omega)
  rwa [show 477696 + (i - 477696) = i by omega] at hk

theorem minUpTo_934 : ∀ i, i < 478720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 478208
  · exact minUpTo_933 i h
  have hk := mBlock934 (i - 478208) (by omega)
  rwa [show 478208 + (i - 478208) = i by omega] at hk

theorem minUpTo_935 : ∀ i, i < 479232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 478720
  · exact minUpTo_934 i h
  have hk := mBlock935 (i - 478720) (by omega)
  rwa [show 478720 + (i - 478720) = i by omega] at hk

theorem minUpTo_936 : ∀ i, i < 479744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 479232
  · exact minUpTo_935 i h
  have hk := mBlock936 (i - 479232) (by omega)
  rwa [show 479232 + (i - 479232) = i by omega] at hk

theorem minUpTo_937 : ∀ i, i < 480256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 479744
  · exact minUpTo_936 i h
  have hk := mBlock937 (i - 479744) (by omega)
  rwa [show 479744 + (i - 479744) = i by omega] at hk

theorem minUpTo_938 : ∀ i, i < 480768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 480256
  · exact minUpTo_937 i h
  have hk := mBlock938 (i - 480256) (by omega)
  rwa [show 480256 + (i - 480256) = i by omega] at hk

theorem minUpTo_939 : ∀ i, i < 481280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 480768
  · exact minUpTo_938 i h
  have hk := mBlock939 (i - 480768) (by omega)
  rwa [show 480768 + (i - 480768) = i by omega] at hk

theorem minUpTo_940 : ∀ i, i < 481792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 481280
  · exact minUpTo_939 i h
  have hk := mBlock940 (i - 481280) (by omega)
  rwa [show 481280 + (i - 481280) = i by omega] at hk

theorem minUpTo_941 : ∀ i, i < 482304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 481792
  · exact minUpTo_940 i h
  have hk := mBlock941 (i - 481792) (by omega)
  rwa [show 481792 + (i - 481792) = i by omega] at hk

theorem minUpTo_942 : ∀ i, i < 482816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 482304
  · exact minUpTo_941 i h
  have hk := mBlock942 (i - 482304) (by omega)
  rwa [show 482304 + (i - 482304) = i by omega] at hk

theorem minUpTo_943 : ∀ i, i < 483328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 482816
  · exact minUpTo_942 i h
  have hk := mBlock943 (i - 482816) (by omega)
  rwa [show 482816 + (i - 482816) = i by omega] at hk

theorem minUpTo_944 : ∀ i, i < 483840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 483328
  · exact minUpTo_943 i h
  have hk := mBlock944 (i - 483328) (by omega)
  rwa [show 483328 + (i - 483328) = i by omega] at hk

theorem minUpTo_945 : ∀ i, i < 484352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 483840
  · exact minUpTo_944 i h
  have hk := mBlock945 (i - 483840) (by omega)
  rwa [show 483840 + (i - 483840) = i by omega] at hk

theorem minUpTo_946 : ∀ i, i < 484864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 484352
  · exact minUpTo_945 i h
  have hk := mBlock946 (i - 484352) (by omega)
  rwa [show 484352 + (i - 484352) = i by omega] at hk

theorem minUpTo_947 : ∀ i, i < 485376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 484864
  · exact minUpTo_946 i h
  have hk := mBlock947 (i - 484864) (by omega)
  rwa [show 484864 + (i - 484864) = i by omega] at hk

theorem minUpTo_948 : ∀ i, i < 485888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 485376
  · exact minUpTo_947 i h
  have hk := mBlock948 (i - 485376) (by omega)
  rwa [show 485376 + (i - 485376) = i by omega] at hk

theorem minUpTo_949 : ∀ i, i < 486400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 485888
  · exact minUpTo_948 i h
  have hk := mBlock949 (i - 485888) (by omega)
  rwa [show 485888 + (i - 485888) = i by omega] at hk

theorem minUpTo_950 : ∀ i, i < 486912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 486400
  · exact minUpTo_949 i h
  have hk := mBlock950 (i - 486400) (by omega)
  rwa [show 486400 + (i - 486400) = i by omega] at hk

theorem minUpTo_951 : ∀ i, i < 487424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 486912
  · exact minUpTo_950 i h
  have hk := mBlock951 (i - 486912) (by omega)
  rwa [show 486912 + (i - 486912) = i by omega] at hk

theorem minUpTo_952 : ∀ i, i < 487936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 487424
  · exact minUpTo_951 i h
  have hk := mBlock952 (i - 487424) (by omega)
  rwa [show 487424 + (i - 487424) = i by omega] at hk

theorem minUpTo_953 : ∀ i, i < 488448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 487936
  · exact minUpTo_952 i h
  have hk := mBlock953 (i - 487936) (by omega)
  rwa [show 487936 + (i - 487936) = i by omega] at hk

theorem minUpTo_954 : ∀ i, i < 488960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 488448
  · exact minUpTo_953 i h
  have hk := mBlock954 (i - 488448) (by omega)
  rwa [show 488448 + (i - 488448) = i by omega] at hk

theorem minUpTo_955 : ∀ i, i < 489472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 488960
  · exact minUpTo_954 i h
  have hk := mBlock955 (i - 488960) (by omega)
  rwa [show 488960 + (i - 488960) = i by omega] at hk

theorem minUpTo_956 : ∀ i, i < 489984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 489472
  · exact minUpTo_955 i h
  have hk := mBlock956 (i - 489472) (by omega)
  rwa [show 489472 + (i - 489472) = i by omega] at hk

theorem minUpTo_957 : ∀ i, i < 490496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 489984
  · exact minUpTo_956 i h
  have hk := mBlock957 (i - 489984) (by omega)
  rwa [show 489984 + (i - 489984) = i by omega] at hk

theorem minUpTo_958 : ∀ i, i < 491008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 490496
  · exact minUpTo_957 i h
  have hk := mBlock958 (i - 490496) (by omega)
  rwa [show 490496 + (i - 490496) = i by omega] at hk

theorem minUpTo_959 : ∀ i, i < 491520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 491008
  · exact minUpTo_958 i h
  have hk := mBlock959 (i - 491008) (by omega)
  rwa [show 491008 + (i - 491008) = i by omega] at hk

theorem minUpTo_960 : ∀ i, i < 492032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 491520
  · exact minUpTo_959 i h
  have hk := mBlock960 (i - 491520) (by omega)
  rwa [show 491520 + (i - 491520) = i by omega] at hk

theorem minUpTo_961 : ∀ i, i < 492544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 492032
  · exact minUpTo_960 i h
  have hk := mBlock961 (i - 492032) (by omega)
  rwa [show 492032 + (i - 492032) = i by omega] at hk

theorem minUpTo_962 : ∀ i, i < 493056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 492544
  · exact minUpTo_961 i h
  have hk := mBlock962 (i - 492544) (by omega)
  rwa [show 492544 + (i - 492544) = i by omega] at hk

theorem minUpTo_963 : ∀ i, i < 493568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 493056
  · exact minUpTo_962 i h
  have hk := mBlock963 (i - 493056) (by omega)
  rwa [show 493056 + (i - 493056) = i by omega] at hk

theorem minUpTo_964 : ∀ i, i < 494080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 493568
  · exact minUpTo_963 i h
  have hk := mBlock964 (i - 493568) (by omega)
  rwa [show 493568 + (i - 493568) = i by omega] at hk

theorem minUpTo_965 : ∀ i, i < 494592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 494080
  · exact minUpTo_964 i h
  have hk := mBlock965 (i - 494080) (by omega)
  rwa [show 494080 + (i - 494080) = i by omega] at hk

theorem minUpTo_966 : ∀ i, i < 495104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 494592
  · exact minUpTo_965 i h
  have hk := mBlock966 (i - 494592) (by omega)
  rwa [show 494592 + (i - 494592) = i by omega] at hk

theorem minUpTo_967 : ∀ i, i < 495616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 495104
  · exact minUpTo_966 i h
  have hk := mBlock967 (i - 495104) (by omega)
  rwa [show 495104 + (i - 495104) = i by omega] at hk

theorem minUpTo_968 : ∀ i, i < 496128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 495616
  · exact minUpTo_967 i h
  have hk := mBlock968 (i - 495616) (by omega)
  rwa [show 495616 + (i - 495616) = i by omega] at hk

theorem minUpTo_969 : ∀ i, i < 496640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 496128
  · exact minUpTo_968 i h
  have hk := mBlock969 (i - 496128) (by omega)
  rwa [show 496128 + (i - 496128) = i by omega] at hk

theorem minUpTo_970 : ∀ i, i < 497152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 496640
  · exact minUpTo_969 i h
  have hk := mBlock970 (i - 496640) (by omega)
  rwa [show 496640 + (i - 496640) = i by omega] at hk

theorem minUpTo_971 : ∀ i, i < 497664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 497152
  · exact minUpTo_970 i h
  have hk := mBlock971 (i - 497152) (by omega)
  rwa [show 497152 + (i - 497152) = i by omega] at hk

theorem minUpTo_972 : ∀ i, i < 498176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 497664
  · exact minUpTo_971 i h
  have hk := mBlock972 (i - 497664) (by omega)
  rwa [show 497664 + (i - 497664) = i by omega] at hk

theorem minUpTo_973 : ∀ i, i < 498688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 498176
  · exact minUpTo_972 i h
  have hk := mBlock973 (i - 498176) (by omega)
  rwa [show 498176 + (i - 498176) = i by omega] at hk

theorem minUpTo_974 : ∀ i, i < 499200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 498688
  · exact minUpTo_973 i h
  have hk := mBlock974 (i - 498688) (by omega)
  rwa [show 498688 + (i - 498688) = i by omega] at hk

theorem minUpTo_975 : ∀ i, i < 499712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 499200
  · exact minUpTo_974 i h
  have hk := mBlock975 (i - 499200) (by omega)
  rwa [show 499200 + (i - 499200) = i by omega] at hk

theorem minUpTo_976 : ∀ i, i < 500224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 499712
  · exact minUpTo_975 i h
  have hk := mBlock976 (i - 499712) (by omega)
  rwa [show 499712 + (i - 499712) = i by omega] at hk

theorem minUpTo_977 : ∀ i, i < 500736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 500224
  · exact minUpTo_976 i h
  have hk := mBlock977 (i - 500224) (by omega)
  rwa [show 500224 + (i - 500224) = i by omega] at hk

theorem minUpTo_978 : ∀ i, i < 501248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 500736
  · exact minUpTo_977 i h
  have hk := mBlock978 (i - 500736) (by omega)
  rwa [show 500736 + (i - 500736) = i by omega] at hk

theorem minUpTo_979 : ∀ i, i < 501760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 501248
  · exact minUpTo_978 i h
  have hk := mBlock979 (i - 501248) (by omega)
  rwa [show 501248 + (i - 501248) = i by omega] at hk

theorem minUpTo_980 : ∀ i, i < 502272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 501760
  · exact minUpTo_979 i h
  have hk := mBlock980 (i - 501760) (by omega)
  rwa [show 501760 + (i - 501760) = i by omega] at hk

theorem minUpTo_981 : ∀ i, i < 502784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 502272
  · exact minUpTo_980 i h
  have hk := mBlock981 (i - 502272) (by omega)
  rwa [show 502272 + (i - 502272) = i by omega] at hk

theorem minUpTo_982 : ∀ i, i < 503296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 502784
  · exact minUpTo_981 i h
  have hk := mBlock982 (i - 502784) (by omega)
  rwa [show 502784 + (i - 502784) = i by omega] at hk

theorem minUpTo_983 : ∀ i, i < 503808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 503296
  · exact minUpTo_982 i h
  have hk := mBlock983 (i - 503296) (by omega)
  rwa [show 503296 + (i - 503296) = i by omega] at hk

theorem minUpTo_984 : ∀ i, i < 504320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 503808
  · exact minUpTo_983 i h
  have hk := mBlock984 (i - 503808) (by omega)
  rwa [show 503808 + (i - 503808) = i by omega] at hk

theorem minUpTo_985 : ∀ i, i < 504832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 504320
  · exact minUpTo_984 i h
  have hk := mBlock985 (i - 504320) (by omega)
  rwa [show 504320 + (i - 504320) = i by omega] at hk

theorem minUpTo_986 : ∀ i, i < 505344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 504832
  · exact minUpTo_985 i h
  have hk := mBlock986 (i - 504832) (by omega)
  rwa [show 504832 + (i - 504832) = i by omega] at hk

theorem minUpTo_987 : ∀ i, i < 505856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 505344
  · exact minUpTo_986 i h
  have hk := mBlock987 (i - 505344) (by omega)
  rwa [show 505344 + (i - 505344) = i by omega] at hk

theorem minUpTo_988 : ∀ i, i < 506368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 505856
  · exact minUpTo_987 i h
  have hk := mBlock988 (i - 505856) (by omega)
  rwa [show 505856 + (i - 505856) = i by omega] at hk

theorem minUpTo_989 : ∀ i, i < 506880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 506368
  · exact minUpTo_988 i h
  have hk := mBlock989 (i - 506368) (by omega)
  rwa [show 506368 + (i - 506368) = i by omega] at hk

theorem minUpTo_990 : ∀ i, i < 507392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 506880
  · exact minUpTo_989 i h
  have hk := mBlock990 (i - 506880) (by omega)
  rwa [show 506880 + (i - 506880) = i by omega] at hk

theorem minUpTo_991 : ∀ i, i < 507904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 507392
  · exact minUpTo_990 i h
  have hk := mBlock991 (i - 507392) (by omega)
  rwa [show 507392 + (i - 507392) = i by omega] at hk

theorem minUpTo_992 : ∀ i, i < 508416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 507904
  · exact minUpTo_991 i h
  have hk := mBlock992 (i - 507904) (by omega)
  rwa [show 507904 + (i - 507904) = i by omega] at hk

theorem minUpTo_993 : ∀ i, i < 508928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 508416
  · exact minUpTo_992 i h
  have hk := mBlock993 (i - 508416) (by omega)
  rwa [show 508416 + (i - 508416) = i by omega] at hk

theorem minUpTo_994 : ∀ i, i < 509440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 508928
  · exact minUpTo_993 i h
  have hk := mBlock994 (i - 508928) (by omega)
  rwa [show 508928 + (i - 508928) = i by omega] at hk

theorem minUpTo_995 : ∀ i, i < 509952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 509440
  · exact minUpTo_994 i h
  have hk := mBlock995 (i - 509440) (by omega)
  rwa [show 509440 + (i - 509440) = i by omega] at hk

theorem minUpTo_996 : ∀ i, i < 510464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 509952
  · exact minUpTo_995 i h
  have hk := mBlock996 (i - 509952) (by omega)
  rwa [show 509952 + (i - 509952) = i by omega] at hk

theorem minUpTo_997 : ∀ i, i < 510976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 510464
  · exact minUpTo_996 i h
  have hk := mBlock997 (i - 510464) (by omega)
  rwa [show 510464 + (i - 510464) = i by omega] at hk

theorem minUpTo_998 : ∀ i, i < 511488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 510976
  · exact minUpTo_997 i h
  have hk := mBlock998 (i - 510976) (by omega)
  rwa [show 510976 + (i - 510976) = i by omega] at hk

theorem minUpTo_999 : ∀ i, i < 512000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 511488
  · exact minUpTo_998 i h
  have hk := mBlock999 (i - 511488) (by omega)
  rwa [show 511488 + (i - 511488) = i by omega] at hk

theorem minUpTo_1000 : ∀ i, i < 512512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 512000
  · exact minUpTo_999 i h
  have hk := mBlock1000 (i - 512000) (by omega)
  rwa [show 512000 + (i - 512000) = i by omega] at hk

theorem minUpTo_1001 : ∀ i, i < 513024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 512512
  · exact minUpTo_1000 i h
  have hk := mBlock1001 (i - 512512) (by omega)
  rwa [show 512512 + (i - 512512) = i by omega] at hk

theorem minUpTo_1002 : ∀ i, i < 513536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 513024
  · exact minUpTo_1001 i h
  have hk := mBlock1002 (i - 513024) (by omega)
  rwa [show 513024 + (i - 513024) = i by omega] at hk

theorem minUpTo_1003 : ∀ i, i < 514048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 513536
  · exact minUpTo_1002 i h
  have hk := mBlock1003 (i - 513536) (by omega)
  rwa [show 513536 + (i - 513536) = i by omega] at hk

theorem minUpTo_1004 : ∀ i, i < 514560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 514048
  · exact minUpTo_1003 i h
  have hk := mBlock1004 (i - 514048) (by omega)
  rwa [show 514048 + (i - 514048) = i by omega] at hk

theorem minUpTo_1005 : ∀ i, i < 515072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 514560
  · exact minUpTo_1004 i h
  have hk := mBlock1005 (i - 514560) (by omega)
  rwa [show 514560 + (i - 514560) = i by omega] at hk

theorem minUpTo_1006 : ∀ i, i < 515584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 515072
  · exact minUpTo_1005 i h
  have hk := mBlock1006 (i - 515072) (by omega)
  rwa [show 515072 + (i - 515072) = i by omega] at hk

theorem minUpTo_1007 : ∀ i, i < 516096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 515584
  · exact minUpTo_1006 i h
  have hk := mBlock1007 (i - 515584) (by omega)
  rwa [show 515584 + (i - 515584) = i by omega] at hk

theorem minUpTo_1008 : ∀ i, i < 516608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 516096
  · exact minUpTo_1007 i h
  have hk := mBlock1008 (i - 516096) (by omega)
  rwa [show 516096 + (i - 516096) = i by omega] at hk

theorem minUpTo_1009 : ∀ i, i < 517120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 516608
  · exact minUpTo_1008 i h
  have hk := mBlock1009 (i - 516608) (by omega)
  rwa [show 516608 + (i - 516608) = i by omega] at hk

theorem minUpTo_1010 : ∀ i, i < 517632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 517120
  · exact minUpTo_1009 i h
  have hk := mBlock1010 (i - 517120) (by omega)
  rwa [show 517120 + (i - 517120) = i by omega] at hk

theorem minUpTo_1011 : ∀ i, i < 518144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 517632
  · exact minUpTo_1010 i h
  have hk := mBlock1011 (i - 517632) (by omega)
  rwa [show 517632 + (i - 517632) = i by omega] at hk

theorem minUpTo_1012 : ∀ i, i < 518656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 518144
  · exact minUpTo_1011 i h
  have hk := mBlock1012 (i - 518144) (by omega)
  rwa [show 518144 + (i - 518144) = i by omega] at hk

theorem minUpTo_1013 : ∀ i, i < 519168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 518656
  · exact minUpTo_1012 i h
  have hk := mBlock1013 (i - 518656) (by omega)
  rwa [show 518656 + (i - 518656) = i by omega] at hk

theorem minUpTo_1014 : ∀ i, i < 519680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 519168
  · exact minUpTo_1013 i h
  have hk := mBlock1014 (i - 519168) (by omega)
  rwa [show 519168 + (i - 519168) = i by omega] at hk

theorem minUpTo_1015 : ∀ i, i < 520192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 519680
  · exact minUpTo_1014 i h
  have hk := mBlock1015 (i - 519680) (by omega)
  rwa [show 519680 + (i - 519680) = i by omega] at hk

theorem minUpTo_1016 : ∀ i, i < 520704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 520192
  · exact minUpTo_1015 i h
  have hk := mBlock1016 (i - 520192) (by omega)
  rwa [show 520192 + (i - 520192) = i by omega] at hk

theorem minUpTo_1017 : ∀ i, i < 521216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 520704
  · exact minUpTo_1016 i h
  have hk := mBlock1017 (i - 520704) (by omega)
  rwa [show 520704 + (i - 520704) = i by omega] at hk

theorem minUpTo_1018 : ∀ i, i < 521728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 521216
  · exact minUpTo_1017 i h
  have hk := mBlock1018 (i - 521216) (by omega)
  rwa [show 521216 + (i - 521216) = i by omega] at hk

theorem minUpTo_1019 : ∀ i, i < 522240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 521728
  · exact minUpTo_1018 i h
  have hk := mBlock1019 (i - 521728) (by omega)
  rwa [show 521728 + (i - 521728) = i by omega] at hk

theorem minUpTo_1020 : ∀ i, i < 522752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 522240
  · exact minUpTo_1019 i h
  have hk := mBlock1020 (i - 522240) (by omega)
  rwa [show 522240 + (i - 522240) = i by omega] at hk

theorem minUpTo_1021 : ∀ i, i < 523264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 522752
  · exact minUpTo_1020 i h
  have hk := mBlock1021 (i - 522752) (by omega)
  rwa [show 522752 + (i - 522752) = i by omega] at hk

theorem minUpTo_1022 : ∀ i, i < 523776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 523264
  · exact minUpTo_1021 i h
  have hk := mBlock1022 (i - 523264) (by omega)
  rwa [show 523264 + (i - 523264) = i by omega] at hk

theorem minUpTo_1023 : ∀ i, i < 524288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 523776
  · exact minUpTo_1022 i h
  have hk := mBlock1023 (i - 523776) (by omega)
  rwa [show 523776 + (i - 523776) = i by omega] at hk

theorem minUpTo_1024 : ∀ i, i < 524800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 524288
  · exact minUpTo_1023 i h
  have hk := mBlock1024 (i - 524288) (by omega)
  rwa [show 524288 + (i - 524288) = i by omega] at hk

theorem minUpTo_1025 : ∀ i, i < 525312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 524800
  · exact minUpTo_1024 i h
  have hk := mBlock1025 (i - 524800) (by omega)
  rwa [show 524800 + (i - 524800) = i by omega] at hk

theorem minUpTo_1026 : ∀ i, i < 525824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 525312
  · exact minUpTo_1025 i h
  have hk := mBlock1026 (i - 525312) (by omega)
  rwa [show 525312 + (i - 525312) = i by omega] at hk

theorem minUpTo_1027 : ∀ i, i < 526336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 525824
  · exact minUpTo_1026 i h
  have hk := mBlock1027 (i - 525824) (by omega)
  rwa [show 525824 + (i - 525824) = i by omega] at hk

theorem minUpTo_1028 : ∀ i, i < 526848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 526336
  · exact minUpTo_1027 i h
  have hk := mBlock1028 (i - 526336) (by omega)
  rwa [show 526336 + (i - 526336) = i by omega] at hk

theorem minUpTo_1029 : ∀ i, i < 527360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 526848
  · exact minUpTo_1028 i h
  have hk := mBlock1029 (i - 526848) (by omega)
  rwa [show 526848 + (i - 526848) = i by omega] at hk

theorem minUpTo_1030 : ∀ i, i < 527872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 527360
  · exact minUpTo_1029 i h
  have hk := mBlock1030 (i - 527360) (by omega)
  rwa [show 527360 + (i - 527360) = i by omega] at hk

theorem minUpTo_1031 : ∀ i, i < 528384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 527872
  · exact minUpTo_1030 i h
  have hk := mBlock1031 (i - 527872) (by omega)
  rwa [show 527872 + (i - 527872) = i by omega] at hk

theorem minUpTo_1032 : ∀ i, i < 528896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 528384
  · exact minUpTo_1031 i h
  have hk := mBlock1032 (i - 528384) (by omega)
  rwa [show 528384 + (i - 528384) = i by omega] at hk

theorem minUpTo_1033 : ∀ i, i < 529408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 528896
  · exact minUpTo_1032 i h
  have hk := mBlock1033 (i - 528896) (by omega)
  rwa [show 528896 + (i - 528896) = i by omega] at hk

theorem minUpTo_1034 : ∀ i, i < 529920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 529408
  · exact minUpTo_1033 i h
  have hk := mBlock1034 (i - 529408) (by omega)
  rwa [show 529408 + (i - 529408) = i by omega] at hk

theorem minUpTo_1035 : ∀ i, i < 530432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 529920
  · exact minUpTo_1034 i h
  have hk := mBlock1035 (i - 529920) (by omega)
  rwa [show 529920 + (i - 529920) = i by omega] at hk

theorem minUpTo_1036 : ∀ i, i < 530944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 530432
  · exact minUpTo_1035 i h
  have hk := mBlock1036 (i - 530432) (by omega)
  rwa [show 530432 + (i - 530432) = i by omega] at hk

theorem minUpTo_1037 : ∀ i, i < 531456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 530944
  · exact minUpTo_1036 i h
  have hk := mBlock1037 (i - 530944) (by omega)
  rwa [show 530944 + (i - 530944) = i by omega] at hk

theorem minUpTo_1038 : ∀ i, i < 531968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 531456
  · exact minUpTo_1037 i h
  have hk := mBlock1038 (i - 531456) (by omega)
  rwa [show 531456 + (i - 531456) = i by omega] at hk

theorem minUpTo_1039 : ∀ i, i < 532480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 531968
  · exact minUpTo_1038 i h
  have hk := mBlock1039 (i - 531968) (by omega)
  rwa [show 531968 + (i - 531968) = i by omega] at hk

theorem minUpTo_1040 : ∀ i, i < 532992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 532480
  · exact minUpTo_1039 i h
  have hk := mBlock1040 (i - 532480) (by omega)
  rwa [show 532480 + (i - 532480) = i by omega] at hk

theorem minUpTo_1041 : ∀ i, i < 533504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 532992
  · exact minUpTo_1040 i h
  have hk := mBlock1041 (i - 532992) (by omega)
  rwa [show 532992 + (i - 532992) = i by omega] at hk

theorem minUpTo_1042 : ∀ i, i < 534016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 533504
  · exact minUpTo_1041 i h
  have hk := mBlock1042 (i - 533504) (by omega)
  rwa [show 533504 + (i - 533504) = i by omega] at hk

theorem minUpTo_1043 : ∀ i, i < 534528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 534016
  · exact minUpTo_1042 i h
  have hk := mBlock1043 (i - 534016) (by omega)
  rwa [show 534016 + (i - 534016) = i by omega] at hk

theorem minUpTo_1044 : ∀ i, i < 535040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 534528
  · exact minUpTo_1043 i h
  have hk := mBlock1044 (i - 534528) (by omega)
  rwa [show 534528 + (i - 534528) = i by omega] at hk

theorem minUpTo_1045 : ∀ i, i < 535552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 535040
  · exact minUpTo_1044 i h
  have hk := mBlock1045 (i - 535040) (by omega)
  rwa [show 535040 + (i - 535040) = i by omega] at hk

theorem minUpTo_1046 : ∀ i, i < 536064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 535552
  · exact minUpTo_1045 i h
  have hk := mBlock1046 (i - 535552) (by omega)
  rwa [show 535552 + (i - 535552) = i by omega] at hk

theorem minUpTo_1047 : ∀ i, i < 536576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 536064
  · exact minUpTo_1046 i h
  have hk := mBlock1047 (i - 536064) (by omega)
  rwa [show 536064 + (i - 536064) = i by omega] at hk

theorem minUpTo_1048 : ∀ i, i < 537088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 536576
  · exact minUpTo_1047 i h
  have hk := mBlock1048 (i - 536576) (by omega)
  rwa [show 536576 + (i - 536576) = i by omega] at hk

theorem minUpTo_1049 : ∀ i, i < 537600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 537088
  · exact minUpTo_1048 i h
  have hk := mBlock1049 (i - 537088) (by omega)
  rwa [show 537088 + (i - 537088) = i by omega] at hk

theorem minUpTo_1050 : ∀ i, i < 538112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 537600
  · exact minUpTo_1049 i h
  have hk := mBlock1050 (i - 537600) (by omega)
  rwa [show 537600 + (i - 537600) = i by omega] at hk

theorem minUpTo_1051 : ∀ i, i < 538624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 538112
  · exact minUpTo_1050 i h
  have hk := mBlock1051 (i - 538112) (by omega)
  rwa [show 538112 + (i - 538112) = i by omega] at hk

theorem minUpTo_1052 : ∀ i, i < 539136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 538624
  · exact minUpTo_1051 i h
  have hk := mBlock1052 (i - 538624) (by omega)
  rwa [show 538624 + (i - 538624) = i by omega] at hk

theorem minUpTo_1053 : ∀ i, i < 539648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 539136
  · exact minUpTo_1052 i h
  have hk := mBlock1053 (i - 539136) (by omega)
  rwa [show 539136 + (i - 539136) = i by omega] at hk

theorem minUpTo_1054 : ∀ i, i < 540160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 539648
  · exact minUpTo_1053 i h
  have hk := mBlock1054 (i - 539648) (by omega)
  rwa [show 539648 + (i - 539648) = i by omega] at hk

theorem minUpTo_1055 : ∀ i, i < 540672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 540160
  · exact minUpTo_1054 i h
  have hk := mBlock1055 (i - 540160) (by omega)
  rwa [show 540160 + (i - 540160) = i by omega] at hk

theorem minUpTo_1056 : ∀ i, i < 541184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 540672
  · exact minUpTo_1055 i h
  have hk := mBlock1056 (i - 540672) (by omega)
  rwa [show 540672 + (i - 540672) = i by omega] at hk

theorem minUpTo_1057 : ∀ i, i < 541696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 541184
  · exact minUpTo_1056 i h
  have hk := mBlock1057 (i - 541184) (by omega)
  rwa [show 541184 + (i - 541184) = i by omega] at hk

theorem minUpTo_1058 : ∀ i, i < 542208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 541696
  · exact minUpTo_1057 i h
  have hk := mBlock1058 (i - 541696) (by omega)
  rwa [show 541696 + (i - 541696) = i by omega] at hk

theorem minUpTo_1059 : ∀ i, i < 542720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 542208
  · exact minUpTo_1058 i h
  have hk := mBlock1059 (i - 542208) (by omega)
  rwa [show 542208 + (i - 542208) = i by omega] at hk

theorem minUpTo_1060 : ∀ i, i < 543232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 542720
  · exact minUpTo_1059 i h
  have hk := mBlock1060 (i - 542720) (by omega)
  rwa [show 542720 + (i - 542720) = i by omega] at hk

theorem minUpTo_1061 : ∀ i, i < 543744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 543232
  · exact minUpTo_1060 i h
  have hk := mBlock1061 (i - 543232) (by omega)
  rwa [show 543232 + (i - 543232) = i by omega] at hk

theorem minUpTo_1062 : ∀ i, i < 544256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 543744
  · exact minUpTo_1061 i h
  have hk := mBlock1062 (i - 543744) (by omega)
  rwa [show 543744 + (i - 543744) = i by omega] at hk

theorem minUpTo_1063 : ∀ i, i < 544768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 544256
  · exact minUpTo_1062 i h
  have hk := mBlock1063 (i - 544256) (by omega)
  rwa [show 544256 + (i - 544256) = i by omega] at hk

theorem minUpTo_1064 : ∀ i, i < 545280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 544768
  · exact minUpTo_1063 i h
  have hk := mBlock1064 (i - 544768) (by omega)
  rwa [show 544768 + (i - 544768) = i by omega] at hk

theorem minUpTo_1065 : ∀ i, i < 545792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 545280
  · exact minUpTo_1064 i h
  have hk := mBlock1065 (i - 545280) (by omega)
  rwa [show 545280 + (i - 545280) = i by omega] at hk

theorem minUpTo_1066 : ∀ i, i < 546304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 545792
  · exact minUpTo_1065 i h
  have hk := mBlock1066 (i - 545792) (by omega)
  rwa [show 545792 + (i - 545792) = i by omega] at hk

theorem minUpTo_1067 : ∀ i, i < 546816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 546304
  · exact minUpTo_1066 i h
  have hk := mBlock1067 (i - 546304) (by omega)
  rwa [show 546304 + (i - 546304) = i by omega] at hk

theorem minUpTo_1068 : ∀ i, i < 547328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 546816
  · exact minUpTo_1067 i h
  have hk := mBlock1068 (i - 546816) (by omega)
  rwa [show 546816 + (i - 546816) = i by omega] at hk

theorem minUpTo_1069 : ∀ i, i < 547840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 547328
  · exact minUpTo_1068 i h
  have hk := mBlock1069 (i - 547328) (by omega)
  rwa [show 547328 + (i - 547328) = i by omega] at hk

theorem minUpTo_1070 : ∀ i, i < 548352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 547840
  · exact minUpTo_1069 i h
  have hk := mBlock1070 (i - 547840) (by omega)
  rwa [show 547840 + (i - 547840) = i by omega] at hk

theorem minUpTo_1071 : ∀ i, i < 548864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 548352
  · exact minUpTo_1070 i h
  have hk := mBlock1071 (i - 548352) (by omega)
  rwa [show 548352 + (i - 548352) = i by omega] at hk

theorem minUpTo_1072 : ∀ i, i < 549376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 548864
  · exact minUpTo_1071 i h
  have hk := mBlock1072 (i - 548864) (by omega)
  rwa [show 548864 + (i - 548864) = i by omega] at hk

theorem minUpTo_1073 : ∀ i, i < 549888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 549376
  · exact minUpTo_1072 i h
  have hk := mBlock1073 (i - 549376) (by omega)
  rwa [show 549376 + (i - 549376) = i by omega] at hk

theorem minUpTo_1074 : ∀ i, i < 550400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 549888
  · exact minUpTo_1073 i h
  have hk := mBlock1074 (i - 549888) (by omega)
  rwa [show 549888 + (i - 549888) = i by omega] at hk

theorem minUpTo_1075 : ∀ i, i < 550912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 550400
  · exact minUpTo_1074 i h
  have hk := mBlock1075 (i - 550400) (by omega)
  rwa [show 550400 + (i - 550400) = i by omega] at hk

theorem minUpTo_1076 : ∀ i, i < 551424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 550912
  · exact minUpTo_1075 i h
  have hk := mBlock1076 (i - 550912) (by omega)
  rwa [show 550912 + (i - 550912) = i by omega] at hk

theorem minUpTo_1077 : ∀ i, i < 551936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 551424
  · exact minUpTo_1076 i h
  have hk := mBlock1077 (i - 551424) (by omega)
  rwa [show 551424 + (i - 551424) = i by omega] at hk

theorem minUpTo_1078 : ∀ i, i < 552448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 551936
  · exact minUpTo_1077 i h
  have hk := mBlock1078 (i - 551936) (by omega)
  rwa [show 551936 + (i - 551936) = i by omega] at hk

theorem minUpTo_1079 : ∀ i, i < 552960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 552448
  · exact minUpTo_1078 i h
  have hk := mBlock1079 (i - 552448) (by omega)
  rwa [show 552448 + (i - 552448) = i by omega] at hk

theorem minUpTo_1080 : ∀ i, i < 553472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 552960
  · exact minUpTo_1079 i h
  have hk := mBlock1080 (i - 552960) (by omega)
  rwa [show 552960 + (i - 552960) = i by omega] at hk

theorem minUpTo_1081 : ∀ i, i < 553984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 553472
  · exact minUpTo_1080 i h
  have hk := mBlock1081 (i - 553472) (by omega)
  rwa [show 553472 + (i - 553472) = i by omega] at hk

theorem minUpTo_1082 : ∀ i, i < 554496 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 553984
  · exact minUpTo_1081 i h
  have hk := mBlock1082 (i - 553984) (by omega)
  rwa [show 553984 + (i - 553984) = i by omega] at hk

theorem minUpTo_1083 : ∀ i, i < 555008 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 554496
  · exact minUpTo_1082 i h
  have hk := mBlock1083 (i - 554496) (by omega)
  rwa [show 554496 + (i - 554496) = i by omega] at hk

theorem minUpTo_1084 : ∀ i, i < 555520 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 555008
  · exact minUpTo_1083 i h
  have hk := mBlock1084 (i - 555008) (by omega)
  rwa [show 555008 + (i - 555008) = i by omega] at hk

theorem minUpTo_1085 : ∀ i, i < 556032 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 555520
  · exact minUpTo_1084 i h
  have hk := mBlock1085 (i - 555520) (by omega)
  rwa [show 555520 + (i - 555520) = i by omega] at hk

theorem minUpTo_1086 : ∀ i, i < 556544 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 556032
  · exact minUpTo_1085 i h
  have hk := mBlock1086 (i - 556032) (by omega)
  rwa [show 556032 + (i - 556032) = i by omega] at hk

theorem minUpTo_1087 : ∀ i, i < 557056 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 556544
  · exact minUpTo_1086 i h
  have hk := mBlock1087 (i - 556544) (by omega)
  rwa [show 556544 + (i - 556544) = i by omega] at hk

theorem minUpTo_1088 : ∀ i, i < 557568 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 557056
  · exact minUpTo_1087 i h
  have hk := mBlock1088 (i - 557056) (by omega)
  rwa [show 557056 + (i - 557056) = i by omega] at hk

theorem minUpTo_1089 : ∀ i, i < 558080 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 557568
  · exact minUpTo_1088 i h
  have hk := mBlock1089 (i - 557568) (by omega)
  rwa [show 557568 + (i - 557568) = i by omega] at hk

theorem minUpTo_1090 : ∀ i, i < 558592 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 558080
  · exact minUpTo_1089 i h
  have hk := mBlock1090 (i - 558080) (by omega)
  rwa [show 558080 + (i - 558080) = i by omega] at hk

theorem minUpTo_1091 : ∀ i, i < 559104 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 558592
  · exact minUpTo_1090 i h
  have hk := mBlock1091 (i - 558592) (by omega)
  rwa [show 558592 + (i - 558592) = i by omega] at hk

theorem minUpTo_1092 : ∀ i, i < 559616 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 559104
  · exact minUpTo_1091 i h
  have hk := mBlock1092 (i - 559104) (by omega)
  rwa [show 559104 + (i - 559104) = i by omega] at hk

theorem minUpTo_1093 : ∀ i, i < 560128 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 559616
  · exact minUpTo_1092 i h
  have hk := mBlock1093 (i - 559616) (by omega)
  rwa [show 559616 + (i - 559616) = i by omega] at hk

theorem minUpTo_1094 : ∀ i, i < 560640 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 560128
  · exact minUpTo_1093 i h
  have hk := mBlock1094 (i - 560128) (by omega)
  rwa [show 560128 + (i - 560128) = i by omega] at hk

theorem minUpTo_1095 : ∀ i, i < 561152 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 560640
  · exact minUpTo_1094 i h
  have hk := mBlock1095 (i - 560640) (by omega)
  rwa [show 560640 + (i - 560640) = i by omega] at hk

theorem minUpTo_1096 : ∀ i, i < 561664 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 561152
  · exact minUpTo_1095 i h
  have hk := mBlock1096 (i - 561152) (by omega)
  rwa [show 561152 + (i - 561152) = i by omega] at hk

theorem minUpTo_1097 : ∀ i, i < 562176 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 561664
  · exact minUpTo_1096 i h
  have hk := mBlock1097 (i - 561664) (by omega)
  rwa [show 561664 + (i - 561664) = i by omega] at hk

theorem minUpTo_1098 : ∀ i, i < 562688 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 562176
  · exact minUpTo_1097 i h
  have hk := mBlock1098 (i - 562176) (by omega)
  rwa [show 562176 + (i - 562176) = i by omega] at hk

theorem minUpTo_1099 : ∀ i, i < 563200 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 562688
  · exact minUpTo_1098 i h
  have hk := mBlock1099 (i - 562688) (by omega)
  rwa [show 562688 + (i - 562688) = i by omega] at hk

theorem minUpTo_1100 : ∀ i, i < 563712 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 563200
  · exact minUpTo_1099 i h
  have hk := mBlock1100 (i - 563200) (by omega)
  rwa [show 563200 + (i - 563200) = i by omega] at hk

theorem minUpTo_1101 : ∀ i, i < 564224 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 563712
  · exact minUpTo_1100 i h
  have hk := mBlock1101 (i - 563712) (by omega)
  rwa [show 563712 + (i - 563712) = i by omega] at hk

theorem minUpTo_1102 : ∀ i, i < 564736 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 564224
  · exact minUpTo_1101 i h
  have hk := mBlock1102 (i - 564224) (by omega)
  rwa [show 564224 + (i - 564224) = i by omega] at hk

theorem minUpTo_1103 : ∀ i, i < 565248 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 564736
  · exact minUpTo_1102 i h
  have hk := mBlock1103 (i - 564736) (by omega)
  rwa [show 564736 + (i - 564736) = i by omega] at hk

theorem minUpTo_1104 : ∀ i, i < 565760 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 565248
  · exact minUpTo_1103 i h
  have hk := mBlock1104 (i - 565248) (by omega)
  rwa [show 565248 + (i - 565248) = i by omega] at hk

theorem minUpTo_1105 : ∀ i, i < 566272 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 565760
  · exact minUpTo_1104 i h
  have hk := mBlock1105 (i - 565760) (by omega)
  rwa [show 565760 + (i - 565760) = i by omega] at hk

theorem minUpTo_1106 : ∀ i, i < 566784 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 566272
  · exact minUpTo_1105 i h
  have hk := mBlock1106 (i - 566272) (by omega)
  rwa [show 566272 + (i - 566272) = i by omega] at hk

theorem minUpTo_1107 : ∀ i, i < 567296 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 566784
  · exact minUpTo_1106 i h
  have hk := mBlock1107 (i - 566784) (by omega)
  rwa [show 566784 + (i - 566784) = i by omega] at hk

theorem minUpTo_1108 : ∀ i, i < 567808 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 567296
  · exact minUpTo_1107 i h
  have hk := mBlock1108 (i - 567296) (by omega)
  rwa [show 567296 + (i - 567296) = i by omega] at hk

theorem minUpTo_1109 : ∀ i, i < 568320 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 567808
  · exact minUpTo_1108 i h
  have hk := mBlock1109 (i - 567808) (by omega)
  rwa [show 567808 + (i - 567808) = i by omega] at hk

theorem minUpTo_1110 : ∀ i, i < 568832 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 568320
  · exact minUpTo_1109 i h
  have hk := mBlock1110 (i - 568320) (by omega)
  rwa [show 568320 + (i - 568320) = i by omega] at hk

theorem minUpTo_1111 : ∀ i, i < 569344 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 568832
  · exact minUpTo_1110 i h
  have hk := mBlock1111 (i - 568832) (by omega)
  rwa [show 568832 + (i - 568832) = i by omega] at hk

theorem minUpTo_1112 : ∀ i, i < 569856 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 569344
  · exact minUpTo_1111 i h
  have hk := mBlock1112 (i - 569344) (by omega)
  rwa [show 569344 + (i - 569344) = i by omega] at hk

theorem minUpTo_1113 : ∀ i, i < 570368 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 569856
  · exact minUpTo_1112 i h
  have hk := mBlock1113 (i - 569856) (by omega)
  rwa [show 569856 + (i - 569856) = i by omega] at hk

theorem minUpTo_1114 : ∀ i, i < 570880 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 570368
  · exact minUpTo_1113 i h
  have hk := mBlock1114 (i - 570368) (by omega)
  rwa [show 570368 + (i - 570368) = i by omega] at hk

theorem minUpTo_1115 : ∀ i, i < 571392 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 570880
  · exact minUpTo_1114 i h
  have hk := mBlock1115 (i - 570880) (by omega)
  rwa [show 570880 + (i - 570880) = i by omega] at hk

theorem minUpTo_1116 : ∀ i, i < 571904 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 571392
  · exact minUpTo_1115 i h
  have hk := mBlock1116 (i - 571392) (by omega)
  rwa [show 571392 + (i - 571392) = i by omega] at hk

theorem minUpTo_1117 : ∀ i, i < 572416 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 571904
  · exact minUpTo_1116 i h
  have hk := mBlock1117 (i - 571904) (by omega)
  rwa [show 571904 + (i - 571904) = i by omega] at hk

theorem minUpTo_1118 : ∀ i, i < 572928 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 572416
  · exact minUpTo_1117 i h
  have hk := mBlock1118 (i - 572416) (by omega)
  rwa [show 572416 + (i - 572416) = i by omega] at hk

theorem minUpTo_1119 : ∀ i, i < 573440 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 572928
  · exact minUpTo_1118 i h
  have hk := mBlock1119 (i - 572928) (by omega)
  rwa [show 572928 + (i - 572928) = i by omega] at hk

theorem minUpTo_1120 : ∀ i, i < 573952 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 573440
  · exact minUpTo_1119 i h
  have hk := mBlock1120 (i - 573440) (by omega)
  rwa [show 573440 + (i - 573440) = i by omega] at hk

theorem minUpTo_1121 : ∀ i, i < 574464 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 573952
  · exact minUpTo_1120 i h
  have hk := mBlock1121 (i - 573952) (by omega)
  rwa [show 573952 + (i - 573952) = i by omega] at hk

theorem minUpTo_1122 : ∀ i, i < 574976 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 574464
  · exact minUpTo_1121 i h
  have hk := mBlock1122 (i - 574464) (by omega)
  rwa [show 574464 + (i - 574464) = i by omega] at hk

theorem minUpTo_1123 : ∀ i, i < 575488 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 574976
  · exact minUpTo_1122 i h
  have hk := mBlock1123 (i - 574976) (by omega)
  rwa [show 574976 + (i - 574976) = i by omega] at hk

theorem minUpTo_1124 : ∀ i, i < 576000 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 575488
  · exact minUpTo_1123 i h
  have hk := mBlock1124 (i - 575488) (by omega)
  rwa [show 575488 + (i - 575488) = i by omega] at hk

theorem minUpTo_1125 : ∀ i, i < 576512 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 576000
  · exact minUpTo_1124 i h
  have hk := mBlock1125 (i - 576000) (by omega)
  rwa [show 576000 + (i - 576000) = i by omega] at hk

theorem minUpTo_1126 : ∀ i, i < 577024 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 576512
  · exact minUpTo_1125 i h
  have hk := mBlock1126 (i - 576512) (by omega)
  rwa [show 576512 + (i - 576512) = i by omega] at hk

theorem minUpTo_1127 : ∀ i, i < 577536 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 577024
  · exact minUpTo_1126 i h
  have hk := mBlock1127 (i - 577024) (by omega)
  rwa [show 577024 + (i - 577024) = i by omega] at hk

theorem minUpTo_1128 : ∀ i, i < 578048 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 577536
  · exact minUpTo_1127 i h
  have hk := mBlock1128 (i - 577536) (by omega)
  rwa [show 577536 + (i - 577536) = i by omega] at hk

theorem minUpTo_1129 : ∀ i, i < 578560 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 578048
  · exact minUpTo_1128 i h
  have hk := mBlock1129 (i - 578048) (by omega)
  rwa [show 578048 + (i - 578048) = i by omega] at hk

theorem minUpTo_1130 : ∀ i, i < 579072 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 578560
  · exact minUpTo_1129 i h
  have hk := mBlock1130 (i - 578560) (by omega)
  rwa [show 578560 + (i - 578560) = i by omega] at hk

theorem minUpTo_1131 : ∀ i, i < 579584 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 579072
  · exact minUpTo_1130 i h
  have hk := mBlock1131 (i - 579072) (by omega)
  rwa [show 579072 + (i - 579072) = i by omega] at hk

theorem minUpTo_1132 : ∀ i, i < 580096 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 579584
  · exact minUpTo_1131 i h
  have hk := mBlock1132 (i - 579584) (by omega)
  rwa [show 579584 + (i - 579584) = i by omega] at hk

theorem minUpTo_1133 : ∀ i, i < 580608 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 580096
  · exact minUpTo_1132 i h
  have hk := mBlock1133 (i - 580096) (by omega)
  rwa [show 580096 + (i - 580096) = i by omega] at hk

theorem minUpTo_1134 : ∀ i, i < 581120 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 580608
  · exact minUpTo_1133 i h
  have hk := mBlock1134 (i - 580608) (by omega)
  rwa [show 580608 + (i - 580608) = i by omega] at hk

theorem minUpTo_1135 : ∀ i, i < 581632 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 581120
  · exact minUpTo_1134 i h
  have hk := mBlock1135 (i - 581120) (by omega)
  rwa [show 581120 + (i - 581120) = i by omega] at hk

theorem minUpTo_1136 : ∀ i, i < 582144 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 581632
  · exact minUpTo_1135 i h
  have hk := mBlock1136 (i - 581632) (by omega)
  rwa [show 581632 + (i - 581632) = i by omega] at hk

theorem minUpTo_1137 : ∀ i, i < 582656 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 582144
  · exact minUpTo_1136 i h
  have hk := mBlock1137 (i - 582144) (by omega)
  rwa [show 582144 + (i - 582144) = i by omega] at hk

theorem minUpTo_1138 : ∀ i, i < 583168 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 582656
  · exact minUpTo_1137 i h
  have hk := mBlock1138 (i - 582656) (by omega)
  rwa [show 582656 + (i - 582656) = i by omega] at hk

theorem minUpTo_1139 : ∀ i, i < 583680 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 583168
  · exact minUpTo_1138 i h
  have hk := mBlock1139 (i - 583168) (by omega)
  rwa [show 583168 + (i - 583168) = i by omega] at hk

theorem minUpTo_1140 : ∀ i, i < 584192 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 583680
  · exact minUpTo_1139 i h
  have hk := mBlock1140 (i - 583680) (by omega)
  rwa [show 583680 + (i - 583680) = i by omega] at hk

theorem minUpTo_1141 : ∀ i, i < 584704 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 584192
  · exact minUpTo_1140 i h
  have hk := mBlock1141 (i - 584192) (by omega)
  rwa [show 584192 + (i - 584192) = i by omega] at hk

theorem minUpTo_1142 : ∀ i, i < 585216 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 584704
  · exact minUpTo_1141 i h
  have hk := mBlock1142 (i - 584704) (by omega)
  rwa [show 584704 + (i - 584704) = i by omega] at hk

theorem minUpTo_1143 : ∀ i, i < 585728 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 585216
  · exact minUpTo_1142 i h
  have hk := mBlock1143 (i - 585216) (by omega)
  rwa [show 585216 + (i - 585216) = i by omega] at hk

theorem minUpTo_1144 : ∀ i, i < 586240 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 585728
  · exact minUpTo_1143 i h
  have hk := mBlock1144 (i - 585728) (by omega)
  rwa [show 585728 + (i - 585728) = i by omega] at hk

theorem minUpTo_1145 : ∀ i, i < 586752 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 586240
  · exact minUpTo_1144 i h
  have hk := mBlock1145 (i - 586240) (by omega)
  rwa [show 586240 + (i - 586240) = i by omega] at hk

theorem minUpTo_1146 : ∀ i, i < 587264 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 586752
  · exact minUpTo_1145 i h
  have hk := mBlock1146 (i - 586752) (by omega)
  rwa [show 586752 + (i - 586752) = i by omega] at hk

theorem minUpTo_1147 : ∀ i, i < 587776 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 587264
  · exact minUpTo_1146 i h
  have hk := mBlock1147 (i - 587264) (by omega)
  rwa [show 587264 + (i - 587264) = i by omega] at hk

theorem minUpTo_1148 : ∀ i, i < 588288 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 587776
  · exact minUpTo_1147 i h
  have hk := mBlock1148 (i - 587776) (by omega)
  rwa [show 587776 + (i - 587776) = i by omega] at hk

theorem minUpTo_1149 : ∀ i, i < 588800 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 588288
  · exact minUpTo_1148 i h
  have hk := mBlock1149 (i - 588288) (by omega)
  rwa [show 588288 + (i - 588288) = i by omega] at hk

theorem minUpTo_1150 : ∀ i, i < 589312 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 588800
  · exact minUpTo_1149 i h
  have hk := mBlock1150 (i - 588800) (by omega)
  rwa [show 588800 + (i - 588800) = i by omega] at hk

theorem minUpTo_1151 : ∀ i, i < 589824 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 589312
  · exact minUpTo_1150 i h
  have hk := mBlock1151 (i - 589312) (by omega)
  rwa [show 589312 + (i - 589312) = i by omega] at hk

theorem minUpTo_1152 : ∀ i, i < 590336 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 589824
  · exact minUpTo_1151 i h
  have hk := mBlock1152 (i - 589824) (by omega)
  rwa [show 589824 + (i - 589824) = i by omega] at hk

theorem minUpTo_1153 : ∀ i, i < 590848 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 590336
  · exact minUpTo_1152 i h
  have hk := mBlock1153 (i - 590336) (by omega)
  rwa [show 590336 + (i - 590336) = i by omega] at hk

theorem minUpTo_1154 : ∀ i, i < 591360 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 590848
  · exact minUpTo_1153 i h
  have hk := mBlock1154 (i - 590848) (by omega)
  rwa [show 590848 + (i - 590848) = i by omega] at hk

theorem minUpTo_1155 : ∀ i, i < 591872 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 591360
  · exact minUpTo_1154 i h
  have hk := mBlock1155 (i - 591360) (by omega)
  rwa [show 591360 + (i - 591360) = i by omega] at hk

theorem minUpTo_1156 : ∀ i, i < 592384 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 591872
  · exact minUpTo_1155 i h
  have hk := mBlock1156 (i - 591872) (by omega)
  rwa [show 591872 + (i - 591872) = i by omega] at hk

theorem minUpTo_1157 : ∀ i, i < 592896 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 592384
  · exact minUpTo_1156 i h
  have hk := mBlock1157 (i - 592384) (by omega)
  rwa [show 592384 + (i - 592384) = i by omega] at hk

theorem minUpTo_1158 : ∀ i, i < 593408 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 592896
  · exact minUpTo_1157 i h
  have hk := mBlock1158 (i - 592896) (by omega)
  rwa [show 592896 + (i - 592896) = i by omega] at hk

theorem minUpTo_1159 : ∀ i, i < 593920 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 593408
  · exact minUpTo_1158 i h
  have hk := mBlock1159 (i - 593408) (by omega)
  rwa [show 593408 + (i - 593408) = i by omega] at hk

theorem minUpTo_1160 : ∀ i, i < 594432 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 593920
  · exact minUpTo_1159 i h
  have hk := mBlock1160 (i - 593920) (by omega)
  rwa [show 593920 + (i - 593920) = i by omega] at hk

theorem minUpTo_1161 : ∀ i, i < 594944 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 594432
  · exact minUpTo_1160 i h
  have hk := mBlock1161 (i - 594432) (by omega)
  rwa [show 594432 + (i - 594432) = i by omega] at hk

theorem minUpTo_1162 : ∀ i, i < 595456 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 594944
  · exact minUpTo_1161 i h
  have hk := mBlock1162 (i - 594944) (by omega)
  rwa [show 594944 + (i - 594944) = i by omega] at hk

theorem minUpTo_1163 : ∀ i, i < 595968 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 595456
  · exact minUpTo_1162 i h
  have hk := mBlock1163 (i - 595456) (by omega)
  rwa [show 595456 + (i - 595456) = i by omega] at hk

theorem minUpTo_1164 : ∀ i, i < 596480 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 595968
  · exact minUpTo_1163 i h
  have hk := mBlock1164 (i - 595968) (by omega)
  rwa [show 595968 + (i - 595968) = i by omega] at hk

theorem minUpTo_1165 : ∀ i, i < 596992 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 596480
  · exact minUpTo_1164 i h
  have hk := mBlock1165 (i - 596480) (by omega)
  rwa [show 596480 + (i - 596480) = i by omega] at hk

theorem minUpTo_1166 : ∀ i, i < 597504 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 596992
  · exact minUpTo_1165 i h
  have hk := mBlock1166 (i - 596992) (by omega)
  rwa [show 596992 + (i - 596992) = i by omega] at hk

theorem minUpTo_1167 : ∀ i, i < 598016 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 597504
  · exact minUpTo_1166 i h
  have hk := mBlock1167 (i - 597504) (by omega)
  rwa [show 597504 + (i - 597504) = i by omega] at hk

theorem minUpTo_1168 : ∀ i, i < 598528 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 598016
  · exact minUpTo_1167 i h
  have hk := mBlock1168 (i - 598016) (by omega)
  rwa [show 598016 + (i - 598016) = i by omega] at hk

theorem minUpTo_1169 : ∀ i, i < 599040 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 598528
  · exact minUpTo_1168 i h
  have hk := mBlock1169 (i - 598528) (by omega)
  rwa [show 598528 + (i - 598528) = i by omega] at hk

theorem minUpTo_1170 : ∀ i, i < 599552 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 599040
  · exact minUpTo_1169 i h
  have hk := mBlock1170 (i - 599040) (by omega)
  rwa [show 599040 + (i - 599040) = i by omega] at hk

theorem minUpTo_1171 : ∀ i, i < 600064 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 599552
  · exact minUpTo_1170 i h
  have hk := mBlock1171 (i - 599552) (by omega)
  rwa [show 599552 + (i - 599552) = i by omega] at hk

theorem minUpTo_1172 : ∀ i, i < 600576 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 600064
  · exact minUpTo_1171 i h
  have hk := mBlock1172 (i - 600064) (by omega)
  rwa [show 600064 + (i - 600064) = i by omega] at hk

theorem minUpTo_1173 : ∀ i, i < 601088 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 600576
  · exact minUpTo_1172 i h
  have hk := mBlock1173 (i - 600576) (by omega)
  rwa [show 600576 + (i - 600576) = i by omega] at hk

theorem minUpTo_1174 : ∀ i, i < 601600 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 601088
  · exact minUpTo_1173 i h
  have hk := mBlock1174 (i - 601088) (by omega)
  rwa [show 601088 + (i - 601088) = i by omega] at hk

theorem minUpTo_1175 : ∀ i, i < 602112 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 601600
  · exact minUpTo_1174 i h
  have hk := mBlock1175 (i - 601600) (by omega)
  rwa [show 601600 + (i - 601600) = i by omega] at hk

theorem minUpTo_1176 : ∀ i, i < 602624 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 602112
  · exact minUpTo_1175 i h
  have hk := mBlock1176 (i - 602112) (by omega)
  rwa [show 602112 + (i - 602112) = i by omega] at hk

theorem minUpTo_1177 : ∀ i, i < 603136 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 602624
  · exact minUpTo_1176 i h
  have hk := mBlock1177 (i - 602624) (by omega)
  rwa [show 602624 + (i - 602624) = i by omega] at hk

theorem minUpTo_1178 : ∀ i, i < 603648 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 603136
  · exact minUpTo_1177 i h
  have hk := mBlock1178 (i - 603136) (by omega)
  rwa [show 603136 + (i - 603136) = i by omega] at hk

theorem minUpTo_1179 : ∀ i, i < 604160 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 603648
  · exact minUpTo_1178 i h
  have hk := mBlock1179 (i - 603648) (by omega)
  rwa [show 603648 + (i - 603648) = i by omega] at hk

theorem minUpTo_1180 : ∀ i, i < 604672 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 604160
  · exact minUpTo_1179 i h
  have hk := mBlock1180 (i - 604160) (by omega)
  rwa [show 604160 + (i - 604160) = i by omega] at hk

theorem minUpTo_1181 : ∀ i, i < 605184 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 604672
  · exact minUpTo_1180 i h
  have hk := mBlock1181 (i - 604672) (by omega)
  rwa [show 604672 + (i - 604672) = i by omega] at hk

theorem minUpTo_1182 : ∀ i, i < 605696 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 605184
  · exact minUpTo_1181 i h
  have hk := mBlock1182 (i - 605184) (by omega)
  rwa [show 605184 + (i - 605184) = i by omega] at hk

theorem minUpTo_1183 : ∀ i, i < 606208 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 605696
  · exact minUpTo_1182 i h
  have hk := mBlock1183 (i - 605696) (by omega)
  rwa [show 605696 + (i - 605696) = i by omega] at hk

theorem minUpTo_1184 : ∀ i, i < 606720 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 606208
  · exact minUpTo_1183 i h
  have hk := mBlock1184 (i - 606208) (by omega)
  rwa [show 606208 + (i - 606208) = i by omega] at hk

theorem minUpTo_1185 : ∀ i, i < 607232 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 606720
  · exact minUpTo_1184 i h
  have hk := mBlock1185 (i - 606720) (by omega)
  rwa [show 606720 + (i - 606720) = i by omega] at hk

theorem minUpTo_1186 : ∀ i, i < 607744 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 607232
  · exact minUpTo_1185 i h
  have hk := mBlock1186 (i - 607232) (by omega)
  rwa [show 607232 + (i - 607232) = i by omega] at hk

theorem minUpTo_1187 : ∀ i, i < 608256 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 607744
  · exact minUpTo_1186 i h
  have hk := mBlock1187 (i - 607744) (by omega)
  rwa [show 607744 + (i - 607744) = i by omega] at hk

theorem minUpTo_1188 : ∀ i, i < 608768 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 608256
  · exact minUpTo_1187 i h
  have hk := mBlock1188 (i - 608256) (by omega)
  rwa [show 608256 + (i - 608256) = i by omega] at hk

theorem minUpTo_1189 : ∀ i, i < 609280 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 608768
  · exact minUpTo_1188 i h
  have hk := mBlock1189 (i - 608768) (by omega)
  rwa [show 608768 + (i - 608768) = i by omega] at hk

theorem minUpTo_1190 : ∀ i, i < 609792 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 609280
  · exact minUpTo_1189 i h
  have hk := mBlock1190 (i - 609280) (by omega)
  rwa [show 609280 + (i - 609280) = i by omega] at hk

theorem minUpTo_1191 : ∀ i, i < 610304 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 609792
  · exact minUpTo_1190 i h
  have hk := mBlock1191 (i - 609792) (by omega)
  rwa [show 609792 + (i - 609792) = i by omega] at hk

theorem minUpTo_1192 : ∀ i, i < 610816 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 610304
  · exact minUpTo_1191 i h
  have hk := mBlock1192 (i - 610304) (by omega)
  rwa [show 610304 + (i - 610304) = i by omega] at hk

theorem minUpTo_1193 : ∀ i, i < 611328 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 610816
  · exact minUpTo_1192 i h
  have hk := mBlock1193 (i - 610816) (by omega)
  rwa [show 610816 + (i - 610816) = i by omega] at hk

theorem minUpTo_1194 : ∀ i, i < 611840 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 611328
  · exact minUpTo_1193 i h
  have hk := mBlock1194 (i - 611328) (by omega)
  rwa [show 611328 + (i - 611328) = i by omega] at hk

theorem minUpTo_1195 : ∀ i, i < 612352 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 611840
  · exact minUpTo_1194 i h
  have hk := mBlock1195 (i - 611840) (by omega)
  rwa [show 611840 + (i - 611840) = i by omega] at hk

theorem minUpTo_1196 : ∀ i, i < 612864 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 612352
  · exact minUpTo_1195 i h
  have hk := mBlock1196 (i - 612352) (by omega)
  rwa [show 612352 + (i - 612352) = i by omega] at hk

theorem minUpTo_1197 : ∀ i, i < 613376 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 612864
  · exact minUpTo_1196 i h
  have hk := mBlock1197 (i - 612864) (by omega)
  rwa [show 612864 + (i - 612864) = i by omega] at hk

theorem minUpTo_1198 : ∀ i, i < 613888 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 613376
  · exact minUpTo_1197 i h
  have hk := mBlock1198 (i - 613376) (by omega)
  rwa [show 613376 + (i - 613376) = i by omega] at hk

theorem minUpTo_1199 : ∀ i, i < 614400 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 613888
  · exact minUpTo_1198 i h
  have hk := mBlock1199 (i - 613888) (by omega)
  rwa [show 613888 + (i - 613888) = i by omega] at hk

theorem minUpTo_1200 : ∀ i, i < 614912 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 614400
  · exact minUpTo_1199 i h
  have hk := mBlock1200 (i - 614400) (by omega)
  rwa [show 614400 + (i - 614400) = i by omega] at hk

theorem minUpTo_1201 : ∀ i, i < 615424 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 614912
  · exact minUpTo_1200 i h
  have hk := mBlock1201 (i - 614912) (by omega)
  rwa [show 614912 + (i - 614912) = i by omega] at hk

theorem minUpTo_1202 : ∀ i, i < 615936 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 615424
  · exact minUpTo_1201 i h
  have hk := mBlock1202 (i - 615424) (by omega)
  rwa [show 615424 + (i - 615424) = i by omega] at hk

theorem minUpTo_1203 : ∀ i, i < 616448 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 615936
  · exact minUpTo_1202 i h
  have hk := mBlock1203 (i - 615936) (by omega)
  rwa [show 615936 + (i - 615936) = i by omega] at hk

theorem minUpTo_1204 : ∀ i, i < 616960 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 616448
  · exact minUpTo_1203 i h
  have hk := mBlock1204 (i - 616448) (by omega)
  rwa [show 616448 + (i - 616448) = i by omega] at hk

theorem minUpTo_1205 : ∀ i, i < 617472 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 616960
  · exact minUpTo_1204 i h
  have hk := mBlock1205 (i - 616960) (by omega)
  rwa [show 616960 + (i - 616960) = i by omega] at hk

theorem minUpTo_1206 : ∀ i, i < 617984 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 617472
  · exact minUpTo_1205 i h
  have hk := mBlock1206 (i - 617472) (by omega)
  rwa [show 617472 + (i - 617472) = i by omega] at hk

theorem minUpTo_1207 : ∀ i, i < 618413 → 44 ≤ supportModulus primes (fun j => (patExt i j).interval.lo) := by
  intro i hi
  by_cases h : i < 617984
  · exact minUpTo_1206 i h
  have hk := mBlock1207 (i - 617984) (by omega)
  rwa [show 617984 + (i - 617984) = i by omega] at hk

theorem hmin : ∀ i, 44 ≤ supportModulus primes (fun j => (patterns i j).interval.lo) :=
  fun i => minUpTo_1207 i.val i.isLt
def wexp : ExponentVector 47 := ![2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
theorem hw : (primePatternBoxes patterns ⟨89, by decide⟩).Contains wexp := by decide +kernel
theorem hwmod : supportModulus primes wexp = 44 := by decide +kernel

end UC85.W.U
