import UC85.W.C.S3_16_t19.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_16_t19
open Modulus40 UC85.W.U

private theorem s_16756 : BitRUP.StepValid rupClauses rupHints 16756 := by decide +kernel
private theorem s_16757 : BitRUP.StepValid rupClauses rupHints 16757 := by decide +kernel
private theorem s_16758 : BitRUP.StepValid rupClauses rupHints 16758 := by decide +kernel
private theorem s_16759 : BitRUP.StepValid rupClauses rupHints 16759 := by decide +kernel
theorem sBlock57 : ∀ k < 4, BitRUP.StepValid rupClauses rupHints (16756 + k) := fun k hk =>
  ((Fin.cases s_16756 (Fin.cases s_16757 (Fin.cases s_16758 (Fin.cases s_16759 (fun k => Fin.elim0 k))))) : ∀ k : Fin 4, BitRUP.StepValid rupClauses rupHints (16756 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_16_t19
