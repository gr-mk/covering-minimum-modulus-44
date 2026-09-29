import UC85.W.U.Rays
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.U
open Modulus40

theorem mBlock64 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (32768 + k) j).interval.lo) := by decide +kernel
theorem mBlock65 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (33280 + k) j).interval.lo) := by decide +kernel
theorem mBlock66 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (33792 + k) j).interval.lo) := by decide +kernel
theorem mBlock67 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (34304 + k) j).interval.lo) := by decide +kernel
theorem mBlock68 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (34816 + k) j).interval.lo) := by decide +kernel
theorem mBlock69 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (35328 + k) j).interval.lo) := by decide +kernel
theorem mBlock70 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (35840 + k) j).interval.lo) := by decide +kernel
theorem mBlock71 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (36352 + k) j).interval.lo) := by decide +kernel
theorem mBlock72 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (36864 + k) j).interval.lo) := by decide +kernel
theorem mBlock73 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (37376 + k) j).interval.lo) := by decide +kernel
theorem mBlock74 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (37888 + k) j).interval.lo) := by decide +kernel
theorem mBlock75 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (38400 + k) j).interval.lo) := by decide +kernel
theorem mBlock76 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (38912 + k) j).interval.lo) := by decide +kernel
theorem mBlock77 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (39424 + k) j).interval.lo) := by decide +kernel
theorem mBlock78 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (39936 + k) j).interval.lo) := by decide +kernel
theorem mBlock79 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (40448 + k) j).interval.lo) := by decide +kernel
theorem mBlock80 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (40960 + k) j).interval.lo) := by decide +kernel
theorem mBlock81 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (41472 + k) j).interval.lo) := by decide +kernel
theorem mBlock82 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (41984 + k) j).interval.lo) := by decide +kernel
theorem mBlock83 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (42496 + k) j).interval.lo) := by decide +kernel
theorem mBlock84 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (43008 + k) j).interval.lo) := by decide +kernel
theorem mBlock85 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (43520 + k) j).interval.lo) := by decide +kernel
theorem mBlock86 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (44032 + k) j).interval.lo) := by decide +kernel
theorem mBlock87 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (44544 + k) j).interval.lo) := by decide +kernel
theorem mBlock88 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (45056 + k) j).interval.lo) := by decide +kernel
theorem mBlock89 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (45568 + k) j).interval.lo) := by decide +kernel
theorem mBlock90 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (46080 + k) j).interval.lo) := by decide +kernel
theorem mBlock91 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (46592 + k) j).interval.lo) := by decide +kernel
theorem mBlock92 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (47104 + k) j).interval.lo) := by decide +kernel
theorem mBlock93 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (47616 + k) j).interval.lo) := by decide +kernel
theorem mBlock94 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (48128 + k) j).interval.lo) := by decide +kernel
theorem mBlock95 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (48640 + k) j).interval.lo) := by decide +kernel
theorem mBlock96 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (49152 + k) j).interval.lo) := by decide +kernel
theorem mBlock97 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (49664 + k) j).interval.lo) := by decide +kernel
theorem mBlock98 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (50176 + k) j).interval.lo) := by decide +kernel
theorem mBlock99 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (50688 + k) j).interval.lo) := by decide +kernel
theorem mBlock100 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (51200 + k) j).interval.lo) := by decide +kernel
theorem mBlock101 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (51712 + k) j).interval.lo) := by decide +kernel
theorem mBlock102 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (52224 + k) j).interval.lo) := by decide +kernel
theorem mBlock103 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (52736 + k) j).interval.lo) := by decide +kernel
theorem mBlock104 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (53248 + k) j).interval.lo) := by decide +kernel
theorem mBlock105 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (53760 + k) j).interval.lo) := by decide +kernel
theorem mBlock106 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (54272 + k) j).interval.lo) := by decide +kernel
theorem mBlock107 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (54784 + k) j).interval.lo) := by decide +kernel
theorem mBlock108 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (55296 + k) j).interval.lo) := by decide +kernel
theorem mBlock109 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (55808 + k) j).interval.lo) := by decide +kernel
theorem mBlock110 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (56320 + k) j).interval.lo) := by decide +kernel
theorem mBlock111 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (56832 + k) j).interval.lo) := by decide +kernel
theorem mBlock112 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (57344 + k) j).interval.lo) := by decide +kernel
theorem mBlock113 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (57856 + k) j).interval.lo) := by decide +kernel
theorem mBlock114 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (58368 + k) j).interval.lo) := by decide +kernel
theorem mBlock115 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (58880 + k) j).interval.lo) := by decide +kernel
theorem mBlock116 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (59392 + k) j).interval.lo) := by decide +kernel
theorem mBlock117 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (59904 + k) j).interval.lo) := by decide +kernel
theorem mBlock118 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (60416 + k) j).interval.lo) := by decide +kernel
theorem mBlock119 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (60928 + k) j).interval.lo) := by decide +kernel
theorem mBlock120 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (61440 + k) j).interval.lo) := by decide +kernel
theorem mBlock121 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (61952 + k) j).interval.lo) := by decide +kernel
theorem mBlock122 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (62464 + k) j).interval.lo) := by decide +kernel
theorem mBlock123 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (62976 + k) j).interval.lo) := by decide +kernel
theorem mBlock124 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (63488 + k) j).interval.lo) := by decide +kernel
theorem mBlock125 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (64000 + k) j).interval.lo) := by decide +kernel
theorem mBlock126 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (64512 + k) j).interval.lo) := by decide +kernel
theorem mBlock127 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (65024 + k) j).interval.lo) := by decide +kernel

end UC85.W.U
