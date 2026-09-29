import UC85.W.U.Rays
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.U
open Modulus40

theorem mBlock512 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (262144 + k) j).interval.lo) := by decide +kernel
theorem mBlock513 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (262656 + k) j).interval.lo) := by decide +kernel
theorem mBlock514 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (263168 + k) j).interval.lo) := by decide +kernel
theorem mBlock515 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (263680 + k) j).interval.lo) := by decide +kernel
theorem mBlock516 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (264192 + k) j).interval.lo) := by decide +kernel
theorem mBlock517 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (264704 + k) j).interval.lo) := by decide +kernel
theorem mBlock518 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (265216 + k) j).interval.lo) := by decide +kernel
theorem mBlock519 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (265728 + k) j).interval.lo) := by decide +kernel
theorem mBlock520 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (266240 + k) j).interval.lo) := by decide +kernel
theorem mBlock521 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (266752 + k) j).interval.lo) := by decide +kernel
theorem mBlock522 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (267264 + k) j).interval.lo) := by decide +kernel
theorem mBlock523 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (267776 + k) j).interval.lo) := by decide +kernel
theorem mBlock524 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (268288 + k) j).interval.lo) := by decide +kernel
theorem mBlock525 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (268800 + k) j).interval.lo) := by decide +kernel
theorem mBlock526 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (269312 + k) j).interval.lo) := by decide +kernel
theorem mBlock527 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (269824 + k) j).interval.lo) := by decide +kernel
theorem mBlock528 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (270336 + k) j).interval.lo) := by decide +kernel
theorem mBlock529 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (270848 + k) j).interval.lo) := by decide +kernel
theorem mBlock530 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (271360 + k) j).interval.lo) := by decide +kernel
theorem mBlock531 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (271872 + k) j).interval.lo) := by decide +kernel
theorem mBlock532 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (272384 + k) j).interval.lo) := by decide +kernel
theorem mBlock533 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (272896 + k) j).interval.lo) := by decide +kernel
theorem mBlock534 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (273408 + k) j).interval.lo) := by decide +kernel
theorem mBlock535 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (273920 + k) j).interval.lo) := by decide +kernel
theorem mBlock536 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (274432 + k) j).interval.lo) := by decide +kernel
theorem mBlock537 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (274944 + k) j).interval.lo) := by decide +kernel
theorem mBlock538 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (275456 + k) j).interval.lo) := by decide +kernel
theorem mBlock539 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (275968 + k) j).interval.lo) := by decide +kernel
theorem mBlock540 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (276480 + k) j).interval.lo) := by decide +kernel
theorem mBlock541 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (276992 + k) j).interval.lo) := by decide +kernel
theorem mBlock542 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (277504 + k) j).interval.lo) := by decide +kernel
theorem mBlock543 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (278016 + k) j).interval.lo) := by decide +kernel
theorem mBlock544 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (278528 + k) j).interval.lo) := by decide +kernel
theorem mBlock545 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (279040 + k) j).interval.lo) := by decide +kernel
theorem mBlock546 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (279552 + k) j).interval.lo) := by decide +kernel
theorem mBlock547 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (280064 + k) j).interval.lo) := by decide +kernel
theorem mBlock548 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (280576 + k) j).interval.lo) := by decide +kernel
theorem mBlock549 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (281088 + k) j).interval.lo) := by decide +kernel
theorem mBlock550 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (281600 + k) j).interval.lo) := by decide +kernel
theorem mBlock551 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (282112 + k) j).interval.lo) := by decide +kernel
theorem mBlock552 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (282624 + k) j).interval.lo) := by decide +kernel
theorem mBlock553 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (283136 + k) j).interval.lo) := by decide +kernel
theorem mBlock554 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (283648 + k) j).interval.lo) := by decide +kernel
theorem mBlock555 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (284160 + k) j).interval.lo) := by decide +kernel
theorem mBlock556 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (284672 + k) j).interval.lo) := by decide +kernel
theorem mBlock557 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (285184 + k) j).interval.lo) := by decide +kernel
theorem mBlock558 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (285696 + k) j).interval.lo) := by decide +kernel
theorem mBlock559 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (286208 + k) j).interval.lo) := by decide +kernel
theorem mBlock560 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (286720 + k) j).interval.lo) := by decide +kernel
theorem mBlock561 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (287232 + k) j).interval.lo) := by decide +kernel
theorem mBlock562 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (287744 + k) j).interval.lo) := by decide +kernel
theorem mBlock563 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (288256 + k) j).interval.lo) := by decide +kernel
theorem mBlock564 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (288768 + k) j).interval.lo) := by decide +kernel
theorem mBlock565 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (289280 + k) j).interval.lo) := by decide +kernel
theorem mBlock566 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (289792 + k) j).interval.lo) := by decide +kernel
theorem mBlock567 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (290304 + k) j).interval.lo) := by decide +kernel
theorem mBlock568 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (290816 + k) j).interval.lo) := by decide +kernel
theorem mBlock569 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (291328 + k) j).interval.lo) := by decide +kernel
theorem mBlock570 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (291840 + k) j).interval.lo) := by decide +kernel
theorem mBlock571 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (292352 + k) j).interval.lo) := by decide +kernel
theorem mBlock572 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (292864 + k) j).interval.lo) := by decide +kernel
theorem mBlock573 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (293376 + k) j).interval.lo) := by decide +kernel
theorem mBlock574 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (293888 + k) j).interval.lo) := by decide +kernel
theorem mBlock575 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (294400 + k) j).interval.lo) := by decide +kernel

end UC85.W.U
