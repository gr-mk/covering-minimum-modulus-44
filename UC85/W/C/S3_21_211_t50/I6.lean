import UC85.W.C.S3_21_211_t50.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_211_t50
open Modulus40 UC85.W.U

theorem oBlock96 : ∀ k < 128, E.originOK (origin (12288 + k)) (rupClauses (12288 + k)) = true := by
  decide +kernel
theorem oBlock97 : ∀ k < 128, E.originOK (origin (12416 + k)) (rupClauses (12416 + k)) = true := by
  decide +kernel
theorem oBlock98 : ∀ k < 128, E.originOK (origin (12544 + k)) (rupClauses (12544 + k)) = true := by
  decide +kernel
theorem oBlock99 : ∀ k < 128, E.originOK (origin (12672 + k)) (rupClauses (12672 + k)) = true := by
  decide +kernel
theorem oBlock100 : ∀ k < 128, E.originOK (origin (12800 + k)) (rupClauses (12800 + k)) = true := by
  decide +kernel
theorem oBlock101 : ∀ k < 128, E.originOK (origin (12928 + k)) (rupClauses (12928 + k)) = true := by
  decide +kernel
theorem oBlock102 : ∀ k < 128, E.originOK (origin (13056 + k)) (rupClauses (13056 + k)) = true := by
  decide +kernel
theorem oBlock103 : ∀ k < 128, E.originOK (origin (13184 + k)) (rupClauses (13184 + k)) = true := by
  decide +kernel
theorem oBlock104 : ∀ k < 128, E.originOK (origin (13312 + k)) (rupClauses (13312 + k)) = true := by
  decide +kernel
theorem oBlock105 : ∀ k < 22, E.originOK (origin (13440 + k)) (rupClauses (13440 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_211_t50
