import UC85.W.C.S3_4_t2.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t2
open Modulus40 UC85.W.U

theorem oBlock80 : ∀ k < 128, E.originOK (origin (10240 + k)) (rupClauses (10240 + k)) = true := by
  decide +kernel
theorem oBlock81 : ∀ k < 128, E.originOK (origin (10368 + k)) (rupClauses (10368 + k)) = true := by
  decide +kernel
theorem oBlock82 : ∀ k < 128, E.originOK (origin (10496 + k)) (rupClauses (10496 + k)) = true := by
  decide +kernel
theorem oBlock83 : ∀ k < 128, E.originOK (origin (10624 + k)) (rupClauses (10624 + k)) = true := by
  decide +kernel
theorem oBlock84 : ∀ k < 128, E.originOK (origin (10752 + k)) (rupClauses (10752 + k)) = true := by
  decide +kernel
theorem oBlock85 : ∀ k < 128, E.originOK (origin (10880 + k)) (rupClauses (10880 + k)) = true := by
  decide +kernel
theorem oBlock86 : ∀ k < 128, E.originOK (origin (11008 + k)) (rupClauses (11008 + k)) = true := by
  decide +kernel
theorem oBlock87 : ∀ k < 128, E.originOK (origin (11136 + k)) (rupClauses (11136 + k)) = true := by
  decide +kernel
theorem oBlock88 : ∀ k < 128, E.originOK (origin (11264 + k)) (rupClauses (11264 + k)) = true := by
  decide +kernel
theorem oBlock89 : ∀ k < 128, E.originOK (origin (11392 + k)) (rupClauses (11392 + k)) = true := by
  decide +kernel
theorem oBlock90 : ∀ k < 128, E.originOK (origin (11520 + k)) (rupClauses (11520 + k)) = true := by
  decide +kernel
theorem oBlock91 : ∀ k < 128, E.originOK (origin (11648 + k)) (rupClauses (11648 + k)) = true := by
  decide +kernel
theorem oBlock92 : ∀ k < 128, E.originOK (origin (11776 + k)) (rupClauses (11776 + k)) = true := by
  decide +kernel
theorem oBlock93 : ∀ k < 128, E.originOK (origin (11904 + k)) (rupClauses (11904 + k)) = true := by
  decide +kernel
theorem oBlock94 : ∀ k < 128, E.originOK (origin (12032 + k)) (rupClauses (12032 + k)) = true := by
  decide +kernel
theorem oBlock95 : ∀ k < 128, E.originOK (origin (12160 + k)) (rupClauses (12160 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_4_t2
