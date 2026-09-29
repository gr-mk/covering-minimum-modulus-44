import UC85.W.C.S3_4_t2.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t2
open Modulus40 UC85.W.U

theorem oBlock128 : ∀ k < 128, E.originOK (origin (16384 + k)) (rupClauses (16384 + k)) = true := by
  decide +kernel
theorem oBlock129 : ∀ k < 128, E.originOK (origin (16512 + k)) (rupClauses (16512 + k)) = true := by
  decide +kernel
theorem oBlock130 : ∀ k < 128, E.originOK (origin (16640 + k)) (rupClauses (16640 + k)) = true := by
  decide +kernel
theorem oBlock131 : ∀ k < 128, E.originOK (origin (16768 + k)) (rupClauses (16768 + k)) = true := by
  decide +kernel
theorem oBlock132 : ∀ k < 128, E.originOK (origin (16896 + k)) (rupClauses (16896 + k)) = true := by
  decide +kernel
theorem oBlock133 : ∀ k < 128, E.originOK (origin (17024 + k)) (rupClauses (17024 + k)) = true := by
  decide +kernel
theorem oBlock134 : ∀ k < 128, E.originOK (origin (17152 + k)) (rupClauses (17152 + k)) = true := by
  decide +kernel
theorem oBlock135 : ∀ k < 128, E.originOK (origin (17280 + k)) (rupClauses (17280 + k)) = true := by
  decide +kernel
theorem oBlock136 : ∀ k < 128, E.originOK (origin (17408 + k)) (rupClauses (17408 + k)) = true := by
  decide +kernel
theorem oBlock137 : ∀ k < 128, E.originOK (origin (17536 + k)) (rupClauses (17536 + k)) = true := by
  decide +kernel
theorem oBlock138 : ∀ k < 128, E.originOK (origin (17664 + k)) (rupClauses (17664 + k)) = true := by
  decide +kernel
theorem oBlock139 : ∀ k < 128, E.originOK (origin (17792 + k)) (rupClauses (17792 + k)) = true := by
  decide +kernel
theorem oBlock140 : ∀ k < 128, E.originOK (origin (17920 + k)) (rupClauses (17920 + k)) = true := by
  decide +kernel
theorem oBlock141 : ∀ k < 128, E.originOK (origin (18048 + k)) (rupClauses (18048 + k)) = true := by
  decide +kernel
theorem oBlock142 : ∀ k < 128, E.originOK (origin (18176 + k)) (rupClauses (18176 + k)) = true := by
  decide +kernel
theorem oBlock143 : ∀ k < 128, E.originOK (origin (18304 + k)) (rupClauses (18304 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_4_t2
