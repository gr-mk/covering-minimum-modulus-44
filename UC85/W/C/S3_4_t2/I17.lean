import UC85.W.C.S3_4_t2.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t2
open Modulus40 UC85.W.U

theorem oBlock272 : ∀ k < 128, E.originOK (origin (34816 + k)) (rupClauses (34816 + k)) = true := by
  decide +kernel
theorem oBlock273 : ∀ k < 72, E.originOK (origin (34944 + k)) (rupClauses (34944 + k)) = true := by
  decide +kernel

end UC85.W.C.S3_4_t2
