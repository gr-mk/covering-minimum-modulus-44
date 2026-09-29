import UC85.W.C.S3_14_t17.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_14_t17
open Modulus40 UC85.W.U

private theorem s_8130 : BitRUP.StepValid rupClauses rupHints 8130 := by decide +kernel
private theorem s_8131 : BitRUP.StepValid rupClauses rupHints 8131 := by decide +kernel
private theorem s_8132 : BitRUP.StepValid rupClauses rupHints 8132 := by decide +kernel
theorem sBlock30 : ∀ k < 3, BitRUP.StepValid rupClauses rupHints (8130 + k) := fun k hk =>
  ((Fin.cases s_8130 (Fin.cases s_8131 (Fin.cases s_8132 (fun k => Fin.elim0 k)))) : ∀ k : Fin 3, BitRUP.StepValid rupClauses rupHints (8130 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_14_t17
