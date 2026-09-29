import UC85.W.C.S3_21_173_t43.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_173_t43
open Modulus40 UC85.W.U

theorem oBlock176 : ∀ k < 128, E.originOK (origin (22528 + k)) (rupClauses (22528 + k)) = true := by
  decide +kernel
theorem oBlock177 : ∀ k < 128, E.originOK (origin (22656 + k)) (rupClauses (22656 + k)) = true := by
  decide +kernel
theorem oBlock178 : ∀ k < 128, E.originOK (origin (22784 + k)) (rupClauses (22784 + k)) = true := by
  decide +kernel
theorem oBlock179 : ∀ k < 127, E.originOK (origin (22912 + k)) (rupClauses (22912 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_173_t43
