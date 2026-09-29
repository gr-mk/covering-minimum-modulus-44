import UC85.W.C.S3_17_t20.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_17_t20
open Modulus40 UC85.W.U

theorem oBlock16 : ∀ k < 128, E.originOK (origin (2048 + k)) (rupClauses (2048 + k)) = true := by
  decide +kernel
theorem oBlock17 : ∀ k < 128, E.originOK (origin (2176 + k)) (rupClauses (2176 + k)) = true := by
  decide +kernel
theorem oBlock18 : ∀ k < 128, E.originOK (origin (2304 + k)) (rupClauses (2304 + k)) = true := by
  decide +kernel
theorem oBlock19 : ∀ k < 128, E.originOK (origin (2432 + k)) (rupClauses (2432 + k)) = true := by
  decide +kernel
theorem oBlock20 : ∀ k < 128, E.originOK (origin (2560 + k)) (rupClauses (2560 + k)) = true := by
  decide +kernel
theorem oBlock21 : ∀ k < 128, E.originOK (origin (2688 + k)) (rupClauses (2688 + k)) = true := by
  decide +kernel
theorem oBlock22 : ∀ k < 128, E.originOK (origin (2816 + k)) (rupClauses (2816 + k)) = true := by
  decide +kernel
theorem oBlock23 : ∀ k < 128, E.originOK (origin (2944 + k)) (rupClauses (2944 + k)) = true := by
  decide +kernel
theorem oBlock24 : ∀ k < 128, E.originOK (origin (3072 + k)) (rupClauses (3072 + k)) = true := by
  decide +kernel
theorem oBlock25 : ∀ k < 128, E.originOK (origin (3200 + k)) (rupClauses (3200 + k)) = true := by
  decide +kernel
theorem oBlock26 : ∀ k < 128, E.originOK (origin (3328 + k)) (rupClauses (3328 + k)) = true := by
  decide +kernel
theorem oBlock27 : ∀ k < 128, E.originOK (origin (3456 + k)) (rupClauses (3456 + k)) = true := by
  decide +kernel
theorem oBlock28 : ∀ k < 128, E.originOK (origin (3584 + k)) (rupClauses (3584 + k)) = true := by
  decide +kernel
theorem oBlock29 : ∀ k < 118, E.originOK (origin (3712 + k)) (rupClauses (3712 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_17_t20
