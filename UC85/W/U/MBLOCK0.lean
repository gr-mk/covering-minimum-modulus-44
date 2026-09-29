import UC85.W.U.Rays
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.U
open Modulus40

theorem mBlock0 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (0 + k) j).interval.lo) := by decide +kernel
theorem mBlock1 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (512 + k) j).interval.lo) := by decide +kernel
theorem mBlock2 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (1024 + k) j).interval.lo) := by decide +kernel
theorem mBlock3 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (1536 + k) j).interval.lo) := by decide +kernel
theorem mBlock4 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (2048 + k) j).interval.lo) := by decide +kernel
theorem mBlock5 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (2560 + k) j).interval.lo) := by decide +kernel
theorem mBlock6 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (3072 + k) j).interval.lo) := by decide +kernel
theorem mBlock7 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (3584 + k) j).interval.lo) := by decide +kernel
theorem mBlock8 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (4096 + k) j).interval.lo) := by decide +kernel
theorem mBlock9 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (4608 + k) j).interval.lo) := by decide +kernel
theorem mBlock10 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (5120 + k) j).interval.lo) := by decide +kernel
theorem mBlock11 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (5632 + k) j).interval.lo) := by decide +kernel
theorem mBlock12 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (6144 + k) j).interval.lo) := by decide +kernel
theorem mBlock13 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (6656 + k) j).interval.lo) := by decide +kernel
theorem mBlock14 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (7168 + k) j).interval.lo) := by decide +kernel
theorem mBlock15 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (7680 + k) j).interval.lo) := by decide +kernel
theorem mBlock16 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (8192 + k) j).interval.lo) := by decide +kernel
theorem mBlock17 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (8704 + k) j).interval.lo) := by decide +kernel
theorem mBlock18 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (9216 + k) j).interval.lo) := by decide +kernel
theorem mBlock19 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (9728 + k) j).interval.lo) := by decide +kernel
theorem mBlock20 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (10240 + k) j).interval.lo) := by decide +kernel
theorem mBlock21 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (10752 + k) j).interval.lo) := by decide +kernel
theorem mBlock22 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (11264 + k) j).interval.lo) := by decide +kernel
theorem mBlock23 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (11776 + k) j).interval.lo) := by decide +kernel
theorem mBlock24 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (12288 + k) j).interval.lo) := by decide +kernel
theorem mBlock25 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (12800 + k) j).interval.lo) := by decide +kernel
theorem mBlock26 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (13312 + k) j).interval.lo) := by decide +kernel
theorem mBlock27 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (13824 + k) j).interval.lo) := by decide +kernel
theorem mBlock28 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (14336 + k) j).interval.lo) := by decide +kernel
theorem mBlock29 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (14848 + k) j).interval.lo) := by decide +kernel
theorem mBlock30 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (15360 + k) j).interval.lo) := by decide +kernel
theorem mBlock31 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (15872 + k) j).interval.lo) := by decide +kernel
theorem mBlock32 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (16384 + k) j).interval.lo) := by decide +kernel
theorem mBlock33 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (16896 + k) j).interval.lo) := by decide +kernel
theorem mBlock34 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (17408 + k) j).interval.lo) := by decide +kernel
theorem mBlock35 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (17920 + k) j).interval.lo) := by decide +kernel
theorem mBlock36 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (18432 + k) j).interval.lo) := by decide +kernel
theorem mBlock37 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (18944 + k) j).interval.lo) := by decide +kernel
theorem mBlock38 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (19456 + k) j).interval.lo) := by decide +kernel
theorem mBlock39 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (19968 + k) j).interval.lo) := by decide +kernel
theorem mBlock40 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (20480 + k) j).interval.lo) := by decide +kernel
theorem mBlock41 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (20992 + k) j).interval.lo) := by decide +kernel
theorem mBlock42 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (21504 + k) j).interval.lo) := by decide +kernel
theorem mBlock43 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (22016 + k) j).interval.lo) := by decide +kernel
theorem mBlock44 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (22528 + k) j).interval.lo) := by decide +kernel
theorem mBlock45 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (23040 + k) j).interval.lo) := by decide +kernel
theorem mBlock46 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (23552 + k) j).interval.lo) := by decide +kernel
theorem mBlock47 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (24064 + k) j).interval.lo) := by decide +kernel
theorem mBlock48 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (24576 + k) j).interval.lo) := by decide +kernel
theorem mBlock49 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (25088 + k) j).interval.lo) := by decide +kernel
theorem mBlock50 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (25600 + k) j).interval.lo) := by decide +kernel
theorem mBlock51 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (26112 + k) j).interval.lo) := by decide +kernel
theorem mBlock52 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (26624 + k) j).interval.lo) := by decide +kernel
theorem mBlock53 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (27136 + k) j).interval.lo) := by decide +kernel
theorem mBlock54 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (27648 + k) j).interval.lo) := by decide +kernel
theorem mBlock55 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (28160 + k) j).interval.lo) := by decide +kernel
theorem mBlock56 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (28672 + k) j).interval.lo) := by decide +kernel
theorem mBlock57 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (29184 + k) j).interval.lo) := by decide +kernel
theorem mBlock58 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (29696 + k) j).interval.lo) := by decide +kernel
theorem mBlock59 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (30208 + k) j).interval.lo) := by decide +kernel
theorem mBlock60 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (30720 + k) j).interval.lo) := by decide +kernel
theorem mBlock61 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (31232 + k) j).interval.lo) := by decide +kernel
theorem mBlock62 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (31744 + k) j).interval.lo) := by decide +kernel
theorem mBlock63 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (32256 + k) j).interval.lo) := by decide +kernel

end UC85.W.U
