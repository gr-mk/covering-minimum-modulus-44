import UC85.W.C.S3_4_t3.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_4_t3
open Modulus40 UC85.W.U

private theorem s_101 : BitRUP.StepValid rupClauses rupHints 101 := by decide +kernel
private theorem s_102 : BitRUP.StepValid rupClauses rupHints 102 := by decide +kernel
private theorem s_103 : BitRUP.StepValid rupClauses rupHints 103 := by decide +kernel
private theorem s_104 : BitRUP.StepValid rupClauses rupHints 104 := by decide +kernel
theorem sBlock0 : ∀ k < 4, BitRUP.StepValid rupClauses rupHints (101 + k) := fun k hk =>
  ((Fin.cases s_101 (Fin.cases s_102 (Fin.cases s_103 (Fin.cases s_104 (fun k => Fin.elim0 k))))) : ∀ k : Fin 4, BitRUP.StepValid rupClauses rupHints (101 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_4_t3
