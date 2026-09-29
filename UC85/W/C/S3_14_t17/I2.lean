import UC85.W.C.S3_14_t17.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_14_t17
open Modulus40 UC85.W.U

theorem oBlock32 : ∀ k < 128, E.originOK (origin (4096 + k)) (rupClauses (4096 + k)) = true := by
  decide +kernel
theorem oBlock33 : ∀ k < 66, E.originOK (origin (4224 + k)) (rupClauses (4224 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_14_t17
