import UC85.W.C.S3_21_211_t50.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_211_t50
open Modulus40 UC85.W.U

private theorem s_18070 : BitRUP.StepValid rupClauses rupHints 18070 := by decide +kernel
private theorem s_18071 : BitRUP.StepValid rupClauses rupHints 18071 := by decide +kernel
private theorem s_18072 : BitRUP.StepValid rupClauses rupHints 18072 := by decide +kernel
private theorem s_18073 : BitRUP.StepValid rupClauses rupHints 18073 := by decide +kernel
private theorem s_18074 : BitRUP.StepValid rupClauses rupHints 18074 := by decide +kernel
private theorem s_18075 : BitRUP.StepValid rupClauses rupHints 18075 := by decide +kernel
private theorem s_18076 : BitRUP.StepValid rupClauses rupHints 18076 := by decide +kernel
private theorem s_18077 : BitRUP.StepValid rupClauses rupHints 18077 := by decide +kernel
private theorem s_18078 : BitRUP.StepValid rupClauses rupHints 18078 := by decide +kernel
private theorem s_18079 : BitRUP.StepValid rupClauses rupHints 18079 := by decide +kernel
private theorem s_18080 : BitRUP.StepValid rupClauses rupHints 18080 := by decide +kernel
private theorem s_18081 : BitRUP.StepValid rupClauses rupHints 18081 := by decide +kernel
private theorem s_18082 : BitRUP.StepValid rupClauses rupHints 18082 := by decide +kernel
private theorem s_18083 : BitRUP.StepValid rupClauses rupHints 18083 := by decide +kernel
private theorem s_18084 : BitRUP.StepValid rupClauses rupHints 18084 := by decide +kernel
private theorem s_18085 : BitRUP.StepValid rupClauses rupHints 18085 := by decide +kernel
private theorem s_18086 : BitRUP.StepValid rupClauses rupHints 18086 := by decide +kernel
private theorem s_18087 : BitRUP.StepValid rupClauses rupHints 18087 := by decide +kernel
private theorem s_18088 : BitRUP.StepValid rupClauses rupHints 18088 := by decide +kernel
private theorem s_18089 : BitRUP.StepValid rupClauses rupHints 18089 := by decide +kernel
private theorem s_18090 : BitRUP.StepValid rupClauses rupHints 18090 := by decide +kernel
theorem sBlock36 : ∀ k < 21, BitRUP.StepValid rupClauses rupHints (18070 + k) := fun k hk =>
  ((Fin.cases s_18070 (Fin.cases s_18071 (Fin.cases s_18072 (Fin.cases s_18073 (Fin.cases s_18074 (Fin.cases s_18075 (Fin.cases s_18076 (Fin.cases s_18077 (Fin.cases s_18078 (Fin.cases s_18079 (Fin.cases s_18080 (Fin.cases s_18081 (Fin.cases s_18082 (Fin.cases s_18083 (Fin.cases s_18084 (Fin.cases s_18085 (Fin.cases s_18086 (Fin.cases s_18087 (Fin.cases s_18088 (Fin.cases s_18089 (Fin.cases s_18090 (fun k => Fin.elim0 k)))))))))))))))))))))) : ∀ k : Fin 21, BitRUP.StepValid rupClauses rupHints (18070 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_21_211_t50
