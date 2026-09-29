import UC85.W.C.S3_4_t1.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t1
open Modulus40 UC85.W.U

theorem oBlock160 : ∀ k < 128, E.originOK (origin (20480 + k)) (rupClauses (20480 + k)) = true := by
  decide +kernel
theorem oBlock161 : ∀ k < 128, E.originOK (origin (20608 + k)) (rupClauses (20608 + k)) = true := by
  decide +kernel
theorem oBlock162 : ∀ k < 128, E.originOK (origin (20736 + k)) (rupClauses (20736 + k)) = true := by
  decide +kernel
theorem oBlock163 : ∀ k < 128, E.originOK (origin (20864 + k)) (rupClauses (20864 + k)) = true := by
  decide +kernel
theorem oBlock164 : ∀ k < 83, E.originOK (origin (20992 + k)) (rupClauses (20992 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_4_t1
