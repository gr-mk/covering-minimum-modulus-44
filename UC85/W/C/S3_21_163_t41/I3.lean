import UC85.W.C.S3_21_163_t41.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_163_t41
open Modulus40 UC85.W.U

theorem oBlock48 : ∀ k < 128, E.originOK (origin (6144 + k)) (rupClauses (6144 + k)) = true := by
  decide +kernel
theorem oBlock49 : ∀ k < 128, E.originOK (origin (6272 + k)) (rupClauses (6272 + k)) = true := by
  decide +kernel
theorem oBlock50 : ∀ k < 128, E.originOK (origin (6400 + k)) (rupClauses (6400 + k)) = true := by
  decide +kernel
theorem oBlock51 : ∀ k < 89, E.originOK (origin (6528 + k)) (rupClauses (6528 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_163_t41
