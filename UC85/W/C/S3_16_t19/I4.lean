import UC85.W.C.S3_16_t19.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_16_t19
open Modulus40 UC85.W.U

theorem oBlock64 : ∀ k < 128, E.originOK (origin (8192 + k)) (rupClauses (8192 + k)) = true := by
  decide +kernel
theorem oBlock65 : ∀ k < 128, E.originOK (origin (8320 + k)) (rupClauses (8320 + k)) = true := by
  decide +kernel
theorem oBlock66 : ∀ k < 128, E.originOK (origin (8448 + k)) (rupClauses (8448 + k)) = true := by
  decide +kernel
theorem oBlock67 : ∀ k < 128, E.originOK (origin (8576 + k)) (rupClauses (8576 + k)) = true := by
  decide +kernel
theorem oBlock68 : ∀ k < 128, E.originOK (origin (8704 + k)) (rupClauses (8704 + k)) = true := by
  decide +kernel
theorem oBlock69 : ∀ k < 128, E.originOK (origin (8832 + k)) (rupClauses (8832 + k)) = true := by
  decide +kernel
theorem oBlock70 : ∀ k < 128, E.originOK (origin (8960 + k)) (rupClauses (8960 + k)) = true := by
  decide +kernel
theorem oBlock71 : ∀ k < 128, E.originOK (origin (9088 + k)) (rupClauses (9088 + k)) = true := by
  decide +kernel
theorem oBlock72 : ∀ k < 128, E.originOK (origin (9216 + k)) (rupClauses (9216 + k)) = true := by
  decide +kernel
theorem oBlock73 : ∀ k < 116, E.originOK (origin (9344 + k)) (rupClauses (9344 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_16_t19
