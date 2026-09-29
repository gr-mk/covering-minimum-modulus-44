import UC85.W.C.S3_19_73_t24.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_19_73_t24
open Modulus40 UC85.W.U

theorem oBlock512 : ∀ k < 128, E.originOK (origin (65536 + k)) (rupClauses (65536 + k)) = true := by
  decide +kernel
theorem oBlock513 : ∀ k < 128, E.originOK (origin (65664 + k)) (rupClauses (65664 + k)) = true := by
  decide +kernel
theorem oBlock514 : ∀ k < 128, E.originOK (origin (65792 + k)) (rupClauses (65792 + k)) = true := by
  decide +kernel
theorem oBlock515 : ∀ k < 128, E.originOK (origin (65920 + k)) (rupClauses (65920 + k)) = true := by
  decide +kernel
theorem oBlock516 : ∀ k < 128, E.originOK (origin (66048 + k)) (rupClauses (66048 + k)) = true := by
  decide +kernel
theorem oBlock517 : ∀ k < 128, E.originOK (origin (66176 + k)) (rupClauses (66176 + k)) = true := by
  decide +kernel
theorem oBlock518 : ∀ k < 128, E.originOK (origin (66304 + k)) (rupClauses (66304 + k)) = true := by
  decide +kernel
theorem oBlock519 : ∀ k < 128, E.originOK (origin (66432 + k)) (rupClauses (66432 + k)) = true := by
  decide +kernel
theorem oBlock520 : ∀ k < 128, E.originOK (origin (66560 + k)) (rupClauses (66560 + k)) = true := by
  decide +kernel
theorem oBlock521 : ∀ k < 128, E.originOK (origin (66688 + k)) (rupClauses (66688 + k)) = true := by
  decide +kernel
theorem oBlock522 : ∀ k < 128, E.originOK (origin (66816 + k)) (rupClauses (66816 + k)) = true := by
  decide +kernel
theorem oBlock523 : ∀ k < 128, E.originOK (origin (66944 + k)) (rupClauses (66944 + k)) = true := by
  decide +kernel
theorem oBlock524 : ∀ k < 128, E.originOK (origin (67072 + k)) (rupClauses (67072 + k)) = true := by
  decide +kernel
theorem oBlock525 : ∀ k < 128, E.originOK (origin (67200 + k)) (rupClauses (67200 + k)) = true := by
  decide +kernel
theorem oBlock526 : ∀ k < 128, E.originOK (origin (67328 + k)) (rupClauses (67328 + k)) = true := by
  decide +kernel
theorem oBlock527 : ∀ k < 128, E.originOK (origin (67456 + k)) (rupClauses (67456 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_19_73_t24
