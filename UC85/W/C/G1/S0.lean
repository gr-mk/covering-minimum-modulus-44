import UC85.W.C.G1.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.G1
open Modulus40 UC85.W.U

private theorem s_49 : BitRUP.StepValid rupClauses rupHints 49 := by decide +kernel
private theorem s_50 : BitRUP.StepValid rupClauses rupHints 50 := by decide +kernel
private theorem s_51 : BitRUP.StepValid rupClauses rupHints 51 := by decide +kernel
theorem sBlock0 : ∀ k < 3, BitRUP.StepValid rupClauses rupHints (49 + k) := fun k hk =>
  ((Fin.cases s_49 (Fin.cases s_50 (Fin.cases s_51 (fun k => Fin.elim0 k)))) : ∀ k : Fin 3, BitRUP.StepValid rupClauses rupHints (49 + k.val)) ⟨k, hk⟩

end UC85.W.C.G1
