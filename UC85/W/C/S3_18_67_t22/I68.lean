import UC85.W.C.S3_18_67_t22.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_18_67_t22
open Modulus40 UC85.W.U

theorem oBlock1088 : ∀ k < 120, E.originOK (origin (139264 + k)) (rupClauses (139264 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_18_67_t22
