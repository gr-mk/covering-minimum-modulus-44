import UC85.W.C.S3_21_151_t39.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_151_t39
open Modulus40 UC85.W.U

private theorem s_5817 : BitRUP.StepValid rupClauses rupHints 5817 := by decide +kernel
private theorem s_5818 : BitRUP.StepValid rupClauses rupHints 5818 := by decide +kernel
private theorem s_5819 : BitRUP.StepValid rupClauses rupHints 5819 := by decide +kernel
private theorem s_5820 : BitRUP.StepValid rupClauses rupHints 5820 := by decide +kernel
private theorem s_5821 : BitRUP.StepValid rupClauses rupHints 5821 := by decide +kernel
private theorem s_5822 : BitRUP.StepValid rupClauses rupHints 5822 := by decide +kernel
private theorem s_5823 : BitRUP.StepValid rupClauses rupHints 5823 := by decide +kernel
private theorem s_5824 : BitRUP.StepValid rupClauses rupHints 5824 := by decide +kernel
private theorem s_5825 : BitRUP.StepValid rupClauses rupHints 5825 := by decide +kernel
private theorem s_5826 : BitRUP.StepValid rupClauses rupHints 5826 := by decide +kernel
private theorem s_5827 : BitRUP.StepValid rupClauses rupHints 5827 := by decide +kernel
private theorem s_5828 : BitRUP.StepValid rupClauses rupHints 5828 := by decide +kernel
private theorem s_5829 : BitRUP.StepValid rupClauses rupHints 5829 := by decide +kernel
private theorem s_5830 : BitRUP.StepValid rupClauses rupHints 5830 := by decide +kernel
private theorem s_5831 : BitRUP.StepValid rupClauses rupHints 5831 := by decide +kernel
theorem sBlock17 : ∀ k < 15, BitRUP.StepValid rupClauses rupHints (5817 + k) := fun k hk =>
  ((Fin.cases s_5817 (Fin.cases s_5818 (Fin.cases s_5819 (Fin.cases s_5820 (Fin.cases s_5821 (Fin.cases s_5822 (Fin.cases s_5823 (Fin.cases s_5824 (Fin.cases s_5825 (Fin.cases s_5826 (Fin.cases s_5827 (Fin.cases s_5828 (Fin.cases s_5829 (Fin.cases s_5830 (Fin.cases s_5831 (fun k => Fin.elim0 k)))))))))))))))) : ∀ k : Fin 15, BitRUP.StepValid rupClauses rupHints (5817 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_21_151_t39
