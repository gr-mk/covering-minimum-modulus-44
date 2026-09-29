import UC85.W.C.S3_4_t0.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t0
open Modulus40 UC85.W.U

private theorem s_105 : BitRUP.StepValid rupClauses rupHints 105 := by decide +kernel
private theorem s_106 : BitRUP.StepValid rupClauses rupHints 106 := by decide +kernel
private theorem s_107 : BitRUP.StepValid rupClauses rupHints 107 := by decide +kernel
private theorem s_108 : BitRUP.StepValid rupClauses rupHints 108 := by decide +kernel
private theorem s_109 : BitRUP.StepValid rupClauses rupHints 109 := by decide +kernel
private theorem s_110 : BitRUP.StepValid rupClauses rupHints 110 := by decide +kernel
private theorem s_111 : BitRUP.StepValid rupClauses rupHints 111 := by decide +kernel
private theorem s_112 : BitRUP.StepValid rupClauses rupHints 112 := by decide +kernel
private theorem s_113 : BitRUP.StepValid rupClauses rupHints 113 := by decide +kernel
theorem sBlock0 : ∀ k < 9, BitRUP.StepValid rupClauses rupHints (105 + k) := fun k hk =>
  ((Fin.cases s_105 (Fin.cases s_106 (Fin.cases s_107 (Fin.cases s_108 (Fin.cases s_109 (Fin.cases s_110 (Fin.cases s_111 (Fin.cases s_112 (Fin.cases s_113 (fun k => Fin.elim0 k)))))))))) : ∀ k : Fin 9, BitRUP.StepValid rupClauses rupHints (105 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_4_t0
