import UC85.W.C.S3_21_97_t28.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_97_t28
open Modulus40 UC85.W.U

theorem oBlock112 : ∀ k < 128, E.originOK (origin (14336 + k)) (rupClauses (14336 + k)) = true := by
  decide +kernel
theorem oBlock113 : ∀ k < 128, E.originOK (origin (14464 + k)) (rupClauses (14464 + k)) = true := by
  decide +kernel
theorem oBlock114 : ∀ k < 128, E.originOK (origin (14592 + k)) (rupClauses (14592 + k)) = true := by
  decide +kernel
theorem oBlock115 : ∀ k < 128, E.originOK (origin (14720 + k)) (rupClauses (14720 + k)) = true := by
  decide +kernel
theorem oBlock116 : ∀ k < 128, E.originOK (origin (14848 + k)) (rupClauses (14848 + k)) = true := by
  decide +kernel
theorem oBlock117 : ∀ k < 98, E.originOK (origin (14976 + k)) (rupClauses (14976 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_97_t28
