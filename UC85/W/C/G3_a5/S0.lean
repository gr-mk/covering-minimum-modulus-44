import UC85.W.C.G3_a5.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.G3_a5
open Modulus40 UC85.W.U

private theorem s_22 : BitRUP.StepValid rupClauses rupHints 22 := by decide +kernel
private theorem s_23 : BitRUP.StepValid rupClauses rupHints 23 := by decide +kernel
theorem sBlock0 : ∀ k < 2, BitRUP.StepValid rupClauses rupHints (22 + k) := fun k hk =>
  ((Fin.cases s_22 (Fin.cases s_23 (fun k => Fin.elim0 k))) : ∀ k : Fin 2, BitRUP.StepValid rupClauses rupHints (22 + k.val)) ⟨k, hk⟩

end UC85.W.C.G3_a5
