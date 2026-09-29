import UC85.W.C.S3_20_79_t25.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_20_79_t25
open Modulus40 UC85.W.U

theorem oBlock240 : ∀ k < 128, E.originOK (origin (30720 + k)) (rupClauses (30720 + k)) = true := by
  decide +kernel
theorem oBlock241 : ∀ k < 128, E.originOK (origin (30848 + k)) (rupClauses (30848 + k)) = true := by
  decide +kernel
theorem oBlock242 : ∀ k < 128, E.originOK (origin (30976 + k)) (rupClauses (30976 + k)) = true := by
  decide +kernel
theorem oBlock243 : ∀ k < 128, E.originOK (origin (31104 + k)) (rupClauses (31104 + k)) = true := by
  decide +kernel
theorem oBlock244 : ∀ k < 128, E.originOK (origin (31232 + k)) (rupClauses (31232 + k)) = true := by
  decide +kernel
theorem oBlock245 : ∀ k < 128, E.originOK (origin (31360 + k)) (rupClauses (31360 + k)) = true := by
  decide +kernel
theorem oBlock246 : ∀ k < 128, E.originOK (origin (31488 + k)) (rupClauses (31488 + k)) = true := by
  decide +kernel
theorem oBlock247 : ∀ k < 128, E.originOK (origin (31616 + k)) (rupClauses (31616 + k)) = true := by
  decide +kernel
theorem oBlock248 : ∀ k < 128, E.originOK (origin (31744 + k)) (rupClauses (31744 + k)) = true := by
  decide +kernel
theorem oBlock249 : ∀ k < 103, E.originOK (origin (31872 + k)) (rupClauses (31872 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_20_79_t25
