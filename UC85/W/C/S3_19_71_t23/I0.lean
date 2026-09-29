import UC85.W.C.S3_19_71_t23.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_19_71_t23
open Modulus40 UC85.W.U

theorem oBlock0 : ∀ k < 128, E.originOK (origin (0 + k)) (rupClauses (0 + k)) = true := by
  decide +kernel
theorem oBlock1 : ∀ k < 128, E.originOK (origin (128 + k)) (rupClauses (128 + k)) = true := by
  decide +kernel
theorem oBlock2 : ∀ k < 128, E.originOK (origin (256 + k)) (rupClauses (256 + k)) = true := by
  decide +kernel
theorem oBlock3 : ∀ k < 128, E.originOK (origin (384 + k)) (rupClauses (384 + k)) = true := by
  decide +kernel
theorem oBlock4 : ∀ k < 128, E.originOK (origin (512 + k)) (rupClauses (512 + k)) = true := by
  decide +kernel
theorem oBlock5 : ∀ k < 128, E.originOK (origin (640 + k)) (rupClauses (640 + k)) = true := by
  decide +kernel
theorem oBlock6 : ∀ k < 128, E.originOK (origin (768 + k)) (rupClauses (768 + k)) = true := by
  decide +kernel
theorem oBlock7 : ∀ k < 128, E.originOK (origin (896 + k)) (rupClauses (896 + k)) = true := by
  decide +kernel
theorem oBlock8 : ∀ k < 128, E.originOK (origin (1024 + k)) (rupClauses (1024 + k)) = true := by
  decide +kernel
theorem oBlock9 : ∀ k < 128, E.originOK (origin (1152 + k)) (rupClauses (1152 + k)) = true := by
  decide +kernel
theorem oBlock10 : ∀ k < 128, E.originOK (origin (1280 + k)) (rupClauses (1280 + k)) = true := by
  decide +kernel
theorem oBlock11 : ∀ k < 128, E.originOK (origin (1408 + k)) (rupClauses (1408 + k)) = true := by
  decide +kernel
theorem oBlock12 : ∀ k < 128, E.originOK (origin (1536 + k)) (rupClauses (1536 + k)) = true := by
  decide +kernel
theorem oBlock13 : ∀ k < 128, E.originOK (origin (1664 + k)) (rupClauses (1664 + k)) = true := by
  decide +kernel
theorem oBlock14 : ∀ k < 128, E.originOK (origin (1792 + k)) (rupClauses (1792 + k)) = true := by
  decide +kernel
theorem oBlock15 : ∀ k < 128, E.originOK (origin (1920 + k)) (rupClauses (1920 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_19_71_t23
