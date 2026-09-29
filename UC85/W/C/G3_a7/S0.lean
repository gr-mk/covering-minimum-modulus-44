import UC85.W.C.G3_a7.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.G3_a7
open Modulus40 UC85.W.U

private theorem s_20 : BitRUP.StepValid rupClauses rupHints 20 := by decide +kernel
theorem sBlock0 : ∀ k < 1, BitRUP.StepValid rupClauses rupHints (20 + k) := fun k hk =>
  ((Fin.cases s_20 (fun k => Fin.elim0 k)) : ∀ k : Fin 1, BitRUP.StepValid rupClauses rupHints (20 + k.val)) ⟨k, hk⟩

end UC85.W.C.G3_a7
