import UC85.W.C.S3_21_179_t44.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_179_t44
open Modulus40 UC85.W.U

theorem oBlock16 : ∀ k < 128, E.originOK (origin (2048 + k)) (rupClauses (2048 + k)) = true := by
  decide +kernel
theorem oBlock17 : ∀ k < 128, E.originOK (origin (2176 + k)) (rupClauses (2176 + k)) = true := by
  decide +kernel
theorem oBlock18 : ∀ k < 25, E.originOK (origin (2304 + k)) (rupClauses (2304 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_179_t44
