import UC85.W.C.S3_21_193_t47.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_193_t47
open Modulus40 UC85.W.U

private theorem s_9774 : BitRUP.StepValid rupClauses rupHints 9774 := by decide +kernel
private theorem s_9775 : BitRUP.StepValid rupClauses rupHints 9775 := by decide +kernel
private theorem s_9776 : BitRUP.StepValid rupClauses rupHints 9776 := by decide +kernel
private theorem s_9777 : BitRUP.StepValid rupClauses rupHints 9777 := by decide +kernel
private theorem s_9778 : BitRUP.StepValid rupClauses rupHints 9778 := by decide +kernel
private theorem s_9779 : BitRUP.StepValid rupClauses rupHints 9779 := by decide +kernel
private theorem s_9780 : BitRUP.StepValid rupClauses rupHints 9780 := by decide +kernel
private theorem s_9781 : BitRUP.StepValid rupClauses rupHints 9781 := by decide +kernel
private theorem s_9782 : BitRUP.StepValid rupClauses rupHints 9782 := by decide +kernel
private theorem s_9783 : BitRUP.StepValid rupClauses rupHints 9783 := by decide +kernel
private theorem s_9784 : BitRUP.StepValid rupClauses rupHints 9784 := by decide +kernel
private theorem s_9785 : BitRUP.StepValid rupClauses rupHints 9785 := by decide +kernel
private theorem s_9786 : BitRUP.StepValid rupClauses rupHints 9786 := by decide +kernel
private theorem s_9787 : BitRUP.StepValid rupClauses rupHints 9787 := by decide +kernel
theorem sBlock27 : ∀ k < 14, BitRUP.StepValid rupClauses rupHints (9774 + k) := fun k hk =>
  ((Fin.cases s_9774 (Fin.cases s_9775 (Fin.cases s_9776 (Fin.cases s_9777 (Fin.cases s_9778 (Fin.cases s_9779 (Fin.cases s_9780 (Fin.cases s_9781 (Fin.cases s_9782 (Fin.cases s_9783 (Fin.cases s_9784 (Fin.cases s_9785 (Fin.cases s_9786 (Fin.cases s_9787 (fun k => Fin.elim0 k))))))))))))))) : ∀ k : Fin 14, BitRUP.StepValid rupClauses rupHints (9774 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_21_193_t47
