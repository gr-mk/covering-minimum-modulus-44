import UC85.W.C.S3_21_157_t40.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_157_t40
open Modulus40 UC85.W.U

theorem oBlock48 : ∀ k < 128, E.originOK (origin (6144 + k)) (rupClauses (6144 + k)) = true := by
  decide +kernel
theorem oBlock49 : ∀ k < 128, E.originOK (origin (6272 + k)) (rupClauses (6272 + k)) = true := by
  decide +kernel
theorem oBlock50 : ∀ k < 128, E.originOK (origin (6400 + k)) (rupClauses (6400 + k)) = true := by
  decide +kernel
theorem oBlock51 : ∀ k < 128, E.originOK (origin (6528 + k)) (rupClauses (6528 + k)) = true := by
  decide +kernel
theorem oBlock52 : ∀ k < 128, E.originOK (origin (6656 + k)) (rupClauses (6656 + k)) = true := by
  decide +kernel
theorem oBlock53 : ∀ k < 128, E.originOK (origin (6784 + k)) (rupClauses (6784 + k)) = true := by
  decide +kernel
theorem oBlock54 : ∀ k < 128, E.originOK (origin (6912 + k)) (rupClauses (6912 + k)) = true := by
  decide +kernel
theorem oBlock55 : ∀ k < 128, E.originOK (origin (7040 + k)) (rupClauses (7040 + k)) = true := by
  decide +kernel
theorem oBlock56 : ∀ k < 128, E.originOK (origin (7168 + k)) (rupClauses (7168 + k)) = true := by
  decide +kernel
theorem oBlock57 : ∀ k < 128, E.originOK (origin (7296 + k)) (rupClauses (7296 + k)) = true := by
  decide +kernel
theorem oBlock58 : ∀ k < 121, E.originOK (origin (7424 + k)) (rupClauses (7424 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_157_t40
