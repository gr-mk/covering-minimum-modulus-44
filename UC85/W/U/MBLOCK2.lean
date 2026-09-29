import UC85.W.U.Rays
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.U
open Modulus40

theorem mBlock128 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (65536 + k) j).interval.lo) := by decide +kernel
theorem mBlock129 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (66048 + k) j).interval.lo) := by decide +kernel
theorem mBlock130 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (66560 + k) j).interval.lo) := by decide +kernel
theorem mBlock131 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (67072 + k) j).interval.lo) := by decide +kernel
theorem mBlock132 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (67584 + k) j).interval.lo) := by decide +kernel
theorem mBlock133 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (68096 + k) j).interval.lo) := by decide +kernel
theorem mBlock134 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (68608 + k) j).interval.lo) := by decide +kernel
theorem mBlock135 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (69120 + k) j).interval.lo) := by decide +kernel
theorem mBlock136 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (69632 + k) j).interval.lo) := by decide +kernel
theorem mBlock137 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (70144 + k) j).interval.lo) := by decide +kernel
theorem mBlock138 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (70656 + k) j).interval.lo) := by decide +kernel
theorem mBlock139 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (71168 + k) j).interval.lo) := by decide +kernel
theorem mBlock140 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (71680 + k) j).interval.lo) := by decide +kernel
theorem mBlock141 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (72192 + k) j).interval.lo) := by decide +kernel
theorem mBlock142 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (72704 + k) j).interval.lo) := by decide +kernel
theorem mBlock143 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (73216 + k) j).interval.lo) := by decide +kernel
theorem mBlock144 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (73728 + k) j).interval.lo) := by decide +kernel
theorem mBlock145 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (74240 + k) j).interval.lo) := by decide +kernel
theorem mBlock146 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (74752 + k) j).interval.lo) := by decide +kernel
theorem mBlock147 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (75264 + k) j).interval.lo) := by decide +kernel
theorem mBlock148 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (75776 + k) j).interval.lo) := by decide +kernel
theorem mBlock149 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (76288 + k) j).interval.lo) := by decide +kernel
theorem mBlock150 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (76800 + k) j).interval.lo) := by decide +kernel
theorem mBlock151 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (77312 + k) j).interval.lo) := by decide +kernel
theorem mBlock152 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (77824 + k) j).interval.lo) := by decide +kernel
theorem mBlock153 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (78336 + k) j).interval.lo) := by decide +kernel
theorem mBlock154 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (78848 + k) j).interval.lo) := by decide +kernel
theorem mBlock155 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (79360 + k) j).interval.lo) := by decide +kernel
theorem mBlock156 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (79872 + k) j).interval.lo) := by decide +kernel
theorem mBlock157 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (80384 + k) j).interval.lo) := by decide +kernel
theorem mBlock158 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (80896 + k) j).interval.lo) := by decide +kernel
theorem mBlock159 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (81408 + k) j).interval.lo) := by decide +kernel
theorem mBlock160 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (81920 + k) j).interval.lo) := by decide +kernel
theorem mBlock161 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (82432 + k) j).interval.lo) := by decide +kernel
theorem mBlock162 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (82944 + k) j).interval.lo) := by decide +kernel
theorem mBlock163 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (83456 + k) j).interval.lo) := by decide +kernel
theorem mBlock164 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (83968 + k) j).interval.lo) := by decide +kernel
theorem mBlock165 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (84480 + k) j).interval.lo) := by decide +kernel
theorem mBlock166 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (84992 + k) j).interval.lo) := by decide +kernel
theorem mBlock167 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (85504 + k) j).interval.lo) := by decide +kernel
theorem mBlock168 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (86016 + k) j).interval.lo) := by decide +kernel
theorem mBlock169 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (86528 + k) j).interval.lo) := by decide +kernel
theorem mBlock170 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (87040 + k) j).interval.lo) := by decide +kernel
theorem mBlock171 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (87552 + k) j).interval.lo) := by decide +kernel
theorem mBlock172 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (88064 + k) j).interval.lo) := by decide +kernel
theorem mBlock173 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (88576 + k) j).interval.lo) := by decide +kernel
theorem mBlock174 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (89088 + k) j).interval.lo) := by decide +kernel
theorem mBlock175 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (89600 + k) j).interval.lo) := by decide +kernel
theorem mBlock176 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (90112 + k) j).interval.lo) := by decide +kernel
theorem mBlock177 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (90624 + k) j).interval.lo) := by decide +kernel
theorem mBlock178 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (91136 + k) j).interval.lo) := by decide +kernel
theorem mBlock179 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (91648 + k) j).interval.lo) := by decide +kernel
theorem mBlock180 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (92160 + k) j).interval.lo) := by decide +kernel
theorem mBlock181 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (92672 + k) j).interval.lo) := by decide +kernel
theorem mBlock182 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (93184 + k) j).interval.lo) := by decide +kernel
theorem mBlock183 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (93696 + k) j).interval.lo) := by decide +kernel
theorem mBlock184 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (94208 + k) j).interval.lo) := by decide +kernel
theorem mBlock185 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (94720 + k) j).interval.lo) := by decide +kernel
theorem mBlock186 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (95232 + k) j).interval.lo) := by decide +kernel
theorem mBlock187 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (95744 + k) j).interval.lo) := by decide +kernel
theorem mBlock188 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (96256 + k) j).interval.lo) := by decide +kernel
theorem mBlock189 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (96768 + k) j).interval.lo) := by decide +kernel
theorem mBlock190 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (97280 + k) j).interval.lo) := by decide +kernel
theorem mBlock191 : ∀ k < 512, 44 ≤ supportModulus primes (fun j => (patExt (97792 + k) j).interval.lo) := by decide +kernel

end UC85.W.U
