import UC85.W.C.G3_a8.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.G3_a8
open Modulus40 UC85.W.U

theorem oBlock0 : ∀ k < 19, E.originOK (origin (0 + k)) (rupClauses (0 + k)) = true := by
  decide +kernel

end UC85.W.C.G3_a8
