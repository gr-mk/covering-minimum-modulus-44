import UC85.W.C.S3_10_t11.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_10_t11
open Modulus40 UC85.W.U

private theorem s_11979 : BitRUP.StepValid rupClauses rupHints 11979 := by decide +kernel
private theorem s_11980 : BitRUP.StepValid rupClauses rupHints 11980 := by decide +kernel
private theorem s_11981 : BitRUP.StepValid rupClauses rupHints 11981 := by decide +kernel
private theorem s_11982 : BitRUP.StepValid rupClauses rupHints 11982 := by decide +kernel
private theorem s_11983 : BitRUP.StepValid rupClauses rupHints 11983 := by decide +kernel
private theorem s_11984 : BitRUP.StepValid rupClauses rupHints 11984 := by decide +kernel
private theorem s_11985 : BitRUP.StepValid rupClauses rupHints 11985 := by decide +kernel
private theorem s_11986 : BitRUP.StepValid rupClauses rupHints 11986 := by decide +kernel
private theorem s_11987 : BitRUP.StepValid rupClauses rupHints 11987 := by decide +kernel
theorem sBlock44 : ∀ k < 9, BitRUP.StepValid rupClauses rupHints (11979 + k) := fun k hk =>
  ((Fin.cases s_11979 (Fin.cases s_11980 (Fin.cases s_11981 (Fin.cases s_11982 (Fin.cases s_11983 (Fin.cases s_11984 (Fin.cases s_11985 (Fin.cases s_11986 (Fin.cases s_11987 (fun k => Fin.elim0 k)))))))))) : ∀ k : Fin 9, BitRUP.StepValid rupClauses rupHints (11979 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_10_t11
