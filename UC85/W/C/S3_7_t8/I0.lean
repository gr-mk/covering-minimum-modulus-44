import UC85.W.C.S3_7_t8.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_7_t8
open Modulus40 UC85.W.U

theorem oBlock0 : ∀ k < 128, E.originOK (origin (0 + k)) (rupClauses (0 + k)) = true := by
  decide +kernel
theorem oBlock1 : ∀ k < 128, E.originOK (origin (128 + k)) (rupClauses (128 + k)) = true := by
  decide +kernel
theorem oBlock2 : ∀ k < 10, E.originOK (origin (256 + k)) (rupClauses (256 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_7_t8
