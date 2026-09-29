import UC85.W.C.S3_21_113_t33.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_113_t33
open Modulus40 UC85.W.U

private theorem s_12033 : BitRUP.StepValid rupClauses rupHints 12033 := by decide +kernel
private theorem s_12034 : BitRUP.StepValid rupClauses rupHints 12034 := by decide +kernel
private theorem s_12035 : BitRUP.StepValid rupClauses rupHints 12035 := by decide +kernel
private theorem s_12036 : BitRUP.StepValid rupClauses rupHints 12036 := by decide +kernel
private theorem s_12037 : BitRUP.StepValid rupClauses rupHints 12037 := by decide +kernel
theorem sBlock38 : ∀ k < 5, BitRUP.StepValid rupClauses rupHints (12033 + k) := fun k hk =>
  ((Fin.cases s_12033 (Fin.cases s_12034 (Fin.cases s_12035 (Fin.cases s_12036 (Fin.cases s_12037 (fun k => Fin.elim0 k)))))) : ∀ k : Fin 5, BitRUP.StepValid rupClauses rupHints (12033 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_21_113_t33
