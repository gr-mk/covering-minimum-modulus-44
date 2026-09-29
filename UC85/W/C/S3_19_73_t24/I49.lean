import UC85.W.C.S3_19_73_t24.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_19_73_t24
open Modulus40 UC85.W.U

theorem oBlock784 : ∀ k < 128, E.originOK (origin (100352 + k)) (rupClauses (100352 + k)) = true := by
  decide +kernel
theorem oBlock785 : ∀ k < 128, E.originOK (origin (100480 + k)) (rupClauses (100480 + k)) = true := by
  decide +kernel
theorem oBlock786 : ∀ k < 128, E.originOK (origin (100608 + k)) (rupClauses (100608 + k)) = true := by
  decide +kernel
theorem oBlock787 : ∀ k < 128, E.originOK (origin (100736 + k)) (rupClauses (100736 + k)) = true := by
  decide +kernel
theorem oBlock788 : ∀ k < 128, E.originOK (origin (100864 + k)) (rupClauses (100864 + k)) = true := by
  decide +kernel
theorem oBlock789 : ∀ k < 128, E.originOK (origin (100992 + k)) (rupClauses (100992 + k)) = true := by
  decide +kernel
theorem oBlock790 : ∀ k < 128, E.originOK (origin (101120 + k)) (rupClauses (101120 + k)) = true := by
  decide +kernel
theorem oBlock791 : ∀ k < 17, E.originOK (origin (101248 + k)) (rupClauses (101248 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_19_73_t24
