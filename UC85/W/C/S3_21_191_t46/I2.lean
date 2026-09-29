import UC85.W.C.S3_21_191_t46.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_191_t46
open Modulus40 UC85.W.U

theorem oBlock32 : ∀ k < 128, E.originOK (origin (4096 + k)) (rupClauses (4096 + k)) = true := by
  decide +kernel
theorem oBlock33 : ∀ k < 128, E.originOK (origin (4224 + k)) (rupClauses (4224 + k)) = true := by
  decide +kernel
theorem oBlock34 : ∀ k < 128, E.originOK (origin (4352 + k)) (rupClauses (4352 + k)) = true := by
  decide +kernel
theorem oBlock35 : ∀ k < 128, E.originOK (origin (4480 + k)) (rupClauses (4480 + k)) = true := by
  decide +kernel
theorem oBlock36 : ∀ k < 128, E.originOK (origin (4608 + k)) (rupClauses (4608 + k)) = true := by
  decide +kernel
theorem oBlock37 : ∀ k < 128, E.originOK (origin (4736 + k)) (rupClauses (4736 + k)) = true := by
  decide +kernel
theorem oBlock38 : ∀ k < 95, E.originOK (origin (4864 + k)) (rupClauses (4864 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_191_t46
