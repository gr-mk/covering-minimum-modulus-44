import UC85.W.C.S3_8_t9.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_8_t9
open Modulus40 UC85.W.U

theorem oBlock304 : ∀ k < 128, E.originOK (origin (38912 + k)) (rupClauses (38912 + k)) = true := by
  decide +kernel
theorem oBlock305 : ∀ k < 128, E.originOK (origin (39040 + k)) (rupClauses (39040 + k)) = true := by
  decide +kernel
theorem oBlock306 : ∀ k < 128, E.originOK (origin (39168 + k)) (rupClauses (39168 + k)) = true := by
  decide +kernel
theorem oBlock307 : ∀ k < 128, E.originOK (origin (39296 + k)) (rupClauses (39296 + k)) = true := by
  decide +kernel
theorem oBlock308 : ∀ k < 128, E.originOK (origin (39424 + k)) (rupClauses (39424 + k)) = true := by
  decide +kernel
theorem oBlock309 : ∀ k < 128, E.originOK (origin (39552 + k)) (rupClauses (39552 + k)) = true := by
  decide +kernel
theorem oBlock310 : ∀ k < 22, E.originOK (origin (39680 + k)) (rupClauses (39680 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_8_t9
