import UC85.W.C.S3_5_t4.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_5_t4
open Modulus40 UC85.W.U

private theorem s_125 : BitRUP.StepValid rupClauses rupHints 125 := by decide +kernel
private theorem s_126 : BitRUP.StepValid rupClauses rupHints 126 := by decide +kernel
private theorem s_127 : BitRUP.StepValid rupClauses rupHints 127 := by decide +kernel
private theorem s_128 : BitRUP.StepValid rupClauses rupHints 128 := by decide +kernel
private theorem s_129 : BitRUP.StepValid rupClauses rupHints 129 := by decide +kernel
private theorem s_130 : BitRUP.StepValid rupClauses rupHints 130 := by decide +kernel
private theorem s_131 : BitRUP.StepValid rupClauses rupHints 131 := by decide +kernel
private theorem s_132 : BitRUP.StepValid rupClauses rupHints 132 := by decide +kernel
private theorem s_133 : BitRUP.StepValid rupClauses rupHints 133 := by decide +kernel
private theorem s_134 : BitRUP.StepValid rupClauses rupHints 134 := by decide +kernel
private theorem s_135 : BitRUP.StepValid rupClauses rupHints 135 := by decide +kernel
private theorem s_136 : BitRUP.StepValid rupClauses rupHints 136 := by decide +kernel
private theorem s_137 : BitRUP.StepValid rupClauses rupHints 137 := by decide +kernel
private theorem s_138 : BitRUP.StepValid rupClauses rupHints 138 := by decide +kernel
private theorem s_139 : BitRUP.StepValid rupClauses rupHints 139 := by decide +kernel
private theorem s_140 : BitRUP.StepValid rupClauses rupHints 140 := by decide +kernel
private theorem s_141 : BitRUP.StepValid rupClauses rupHints 141 := by decide +kernel
private theorem s_142 : BitRUP.StepValid rupClauses rupHints 142 := by decide +kernel
theorem sBlock0 : ∀ k < 18, BitRUP.StepValid rupClauses rupHints (125 + k) := fun k hk =>
  ((Fin.cases s_125 (Fin.cases s_126 (Fin.cases s_127 (Fin.cases s_128 (Fin.cases s_129 (Fin.cases s_130 (Fin.cases s_131 (Fin.cases s_132 (Fin.cases s_133 (Fin.cases s_134 (Fin.cases s_135 (Fin.cases s_136 (Fin.cases s_137 (Fin.cases s_138 (Fin.cases s_139 (Fin.cases s_140 (Fin.cases s_141 (Fin.cases s_142 (fun k => Fin.elim0 k))))))))))))))))))) : ∀ k : Fin 18, BitRUP.StepValid rupClauses rupHints (125 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_5_t4
