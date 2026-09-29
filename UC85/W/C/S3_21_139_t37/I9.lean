import UC85.W.C.S3_21_139_t37.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_139_t37
open Modulus40 UC85.W.U

theorem oBlock144 : ∀ k < 128, E.originOK (origin (18432 + k)) (rupClauses (18432 + k)) = true := by
  decide +kernel
theorem oBlock145 : ∀ k < 128, E.originOK (origin (18560 + k)) (rupClauses (18560 + k)) = true := by
  decide +kernel
theorem oBlock146 : ∀ k < 128, E.originOK (origin (18688 + k)) (rupClauses (18688 + k)) = true := by
  decide +kernel
theorem oBlock147 : ∀ k < 128, E.originOK (origin (18816 + k)) (rupClauses (18816 + k)) = true := by
  decide +kernel
theorem oBlock148 : ∀ k < 128, E.originOK (origin (18944 + k)) (rupClauses (18944 + k)) = true := by
  decide +kernel
theorem oBlock149 : ∀ k < 128, E.originOK (origin (19072 + k)) (rupClauses (19072 + k)) = true := by
  decide +kernel
theorem oBlock150 : ∀ k < 85, E.originOK (origin (19200 + k)) (rupClauses (19200 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_21_139_t37
