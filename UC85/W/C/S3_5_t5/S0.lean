import UC85.W.C.S3_5_t5.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_5_t5
open Modulus40 UC85.W.U

private theorem s_112 : BitRUP.StepValid rupClauses rupHints 112 := by decide +kernel
private theorem s_113 : BitRUP.StepValid rupClauses rupHints 113 := by decide +kernel
private theorem s_114 : BitRUP.StepValid rupClauses rupHints 114 := by decide +kernel
private theorem s_115 : BitRUP.StepValid rupClauses rupHints 115 := by decide +kernel
private theorem s_116 : BitRUP.StepValid rupClauses rupHints 116 := by decide +kernel
private theorem s_117 : BitRUP.StepValid rupClauses rupHints 117 := by decide +kernel
private theorem s_118 : BitRUP.StepValid rupClauses rupHints 118 := by decide +kernel
private theorem s_119 : BitRUP.StepValid rupClauses rupHints 119 := by decide +kernel
private theorem s_120 : BitRUP.StepValid rupClauses rupHints 120 := by decide +kernel
private theorem s_121 : BitRUP.StepValid rupClauses rupHints 121 := by decide +kernel
private theorem s_122 : BitRUP.StepValid rupClauses rupHints 122 := by decide +kernel
private theorem s_123 : BitRUP.StepValid rupClauses rupHints 123 := by decide +kernel
private theorem s_124 : BitRUP.StepValid rupClauses rupHints 124 := by decide +kernel
private theorem s_125 : BitRUP.StepValid rupClauses rupHints 125 := by decide +kernel
private theorem s_126 : BitRUP.StepValid rupClauses rupHints 126 := by decide +kernel
private theorem s_127 : BitRUP.StepValid rupClauses rupHints 127 := by decide +kernel
private theorem s_128 : BitRUP.StepValid rupClauses rupHints 128 := by decide +kernel
private theorem s_129 : BitRUP.StepValid rupClauses rupHints 129 := by decide +kernel
private theorem s_130 : BitRUP.StepValid rupClauses rupHints 130 := by decide +kernel
private theorem s_131 : BitRUP.StepValid rupClauses rupHints 131 := by decide +kernel
private theorem s_132 : BitRUP.StepValid rupClauses rupHints 132 := by decide +kernel
private theorem s_133 : BitRUP.StepValid rupClauses rupHints 133 := by decide +kernel
theorem sBlock0 : ∀ k < 22, BitRUP.StepValid rupClauses rupHints (112 + k) := fun k hk =>
  ((Fin.cases s_112 (Fin.cases s_113 (Fin.cases s_114 (Fin.cases s_115 (Fin.cases s_116 (Fin.cases s_117 (Fin.cases s_118 (Fin.cases s_119 (Fin.cases s_120 (Fin.cases s_121 (Fin.cases s_122 (Fin.cases s_123 (Fin.cases s_124 (Fin.cases s_125 (Fin.cases s_126 (Fin.cases s_127 (Fin.cases s_128 (Fin.cases s_129 (Fin.cases s_130 (Fin.cases s_131 (Fin.cases s_132 (Fin.cases s_133 (fun k => Fin.elim0 k))))))))))))))))))))))) : ∀ k : Fin 22, BitRUP.StepValid rupClauses rupHints (112 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_5_t5
