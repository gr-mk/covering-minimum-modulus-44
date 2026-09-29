import UC85.W.C.S3_21_149_t38.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_21_149_t38
open Modulus40 UC85.W.U

private theorem s_5161 : BitRUP.StepValid rupClauses rupHints 5161 := by decide +kernel
private theorem s_5162 : BitRUP.StepValid rupClauses rupHints 5162 := by decide +kernel
private theorem s_5163 : BitRUP.StepValid rupClauses rupHints 5163 := by decide +kernel
private theorem s_5164 : BitRUP.StepValid rupClauses rupHints 5164 := by decide +kernel
private theorem s_5165 : BitRUP.StepValid rupClauses rupHints 5165 := by decide +kernel
private theorem s_5166 : BitRUP.StepValid rupClauses rupHints 5166 := by decide +kernel
private theorem s_5167 : BitRUP.StepValid rupClauses rupHints 5167 := by decide +kernel
private theorem s_5168 : BitRUP.StepValid rupClauses rupHints 5168 := by decide +kernel
private theorem s_5169 : BitRUP.StepValid rupClauses rupHints 5169 := by decide +kernel
private theorem s_5170 : BitRUP.StepValid rupClauses rupHints 5170 := by decide +kernel
private theorem s_5171 : BitRUP.StepValid rupClauses rupHints 5171 := by decide +kernel
private theorem s_5172 : BitRUP.StepValid rupClauses rupHints 5172 := by decide +kernel
private theorem s_5173 : BitRUP.StepValid rupClauses rupHints 5173 := by decide +kernel
private theorem s_5174 : BitRUP.StepValid rupClauses rupHints 5174 := by decide +kernel
private theorem s_5175 : BitRUP.StepValid rupClauses rupHints 5175 := by decide +kernel
private theorem s_5176 : BitRUP.StepValid rupClauses rupHints 5176 := by decide +kernel
private theorem s_5177 : BitRUP.StepValid rupClauses rupHints 5177 := by decide +kernel
private theorem s_5178 : BitRUP.StepValid rupClauses rupHints 5178 := by decide +kernel
private theorem s_5179 : BitRUP.StepValid rupClauses rupHints 5179 := by decide +kernel
private theorem s_5180 : BitRUP.StepValid rupClauses rupHints 5180 := by decide +kernel
private theorem s_5181 : BitRUP.StepValid rupClauses rupHints 5181 := by decide +kernel
private theorem s_5182 : BitRUP.StepValid rupClauses rupHints 5182 := by decide +kernel
private theorem s_5183 : BitRUP.StepValid rupClauses rupHints 5183 := by decide +kernel
private theorem s_5184 : BitRUP.StepValid rupClauses rupHints 5184 := by decide +kernel
private theorem s_5185 : BitRUP.StepValid rupClauses rupHints 5185 := by decide +kernel
private theorem s_5186 : BitRUP.StepValid rupClauses rupHints 5186 := by decide +kernel
private theorem s_5187 : BitRUP.StepValid rupClauses rupHints 5187 := by decide +kernel
private theorem s_5188 : BitRUP.StepValid rupClauses rupHints 5188 := by decide +kernel
private theorem s_5189 : BitRUP.StepValid rupClauses rupHints 5189 := by decide +kernel
private theorem s_5190 : BitRUP.StepValid rupClauses rupHints 5190 := by decide +kernel
private theorem s_5191 : BitRUP.StepValid rupClauses rupHints 5191 := by decide +kernel
private theorem s_5192 : BitRUP.StepValid rupClauses rupHints 5192 := by decide +kernel
theorem sBlock19 : ∀ k < 32, BitRUP.StepValid rupClauses rupHints (5161 + k) := fun k hk =>
  ((Fin.cases s_5161 (Fin.cases s_5162 (Fin.cases s_5163 (Fin.cases s_5164 (Fin.cases s_5165 (Fin.cases s_5166 (Fin.cases s_5167 (Fin.cases s_5168 (Fin.cases s_5169 (Fin.cases s_5170 (Fin.cases s_5171 (Fin.cases s_5172 (Fin.cases s_5173 (Fin.cases s_5174 (Fin.cases s_5175 (Fin.cases s_5176 (Fin.cases s_5177 (Fin.cases s_5178 (Fin.cases s_5179 (Fin.cases s_5180 (Fin.cases s_5181 (Fin.cases s_5182 (Fin.cases s_5183 (Fin.cases s_5184 (Fin.cases s_5185 (Fin.cases s_5186 (Fin.cases s_5187 (Fin.cases s_5188 (Fin.cases s_5189 (Fin.cases s_5190 (Fin.cases s_5191 (Fin.cases s_5192 (fun k => Fin.elim0 k))))))))))))))))))))))))))))))))) : ∀ k : Fin 32, BitRUP.StepValid rupClauses rupHints (5161 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_21_149_t38
