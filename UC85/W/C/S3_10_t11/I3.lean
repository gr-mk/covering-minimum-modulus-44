import UC85.W.C.S3_10_t11.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_10_t11
open Modulus40 UC85.W.U

theorem oBlock48 : ∀ k < 128, E.originOK (origin (6144 + k)) (rupClauses (6144 + k)) = true := by
  decide +kernel
theorem oBlock49 : ∀ k < 75, E.originOK (origin (6272 + k)) (rupClauses (6272 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_10_t11
