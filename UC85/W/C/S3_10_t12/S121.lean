import UC85.W.C.S3_10_t12.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_10_t12
open Modulus40 UC85.W.U

private theorem s_31005 : BitRUP.StepValid rupClauses rupHints 31005 := by decide +kernel
private theorem s_31006 : BitRUP.StepValid rupClauses rupHints 31006 := by decide +kernel
private theorem s_31007 : BitRUP.StepValid rupClauses rupHints 31007 := by decide +kernel
private theorem s_31008 : BitRUP.StepValid rupClauses rupHints 31008 := by decide +kernel
private theorem s_31009 : BitRUP.StepValid rupClauses rupHints 31009 := by decide +kernel
private theorem s_31010 : BitRUP.StepValid rupClauses rupHints 31010 := by decide +kernel
private theorem s_31011 : BitRUP.StepValid rupClauses rupHints 31011 := by decide +kernel
private theorem s_31012 : BitRUP.StepValid rupClauses rupHints 31012 := by decide +kernel
private theorem s_31013 : BitRUP.StepValid rupClauses rupHints 31013 := by decide +kernel
private theorem s_31014 : BitRUP.StepValid rupClauses rupHints 31014 := by decide +kernel
private theorem s_31015 : BitRUP.StepValid rupClauses rupHints 31015 := by decide +kernel
private theorem s_31016 : BitRUP.StepValid rupClauses rupHints 31016 := by decide +kernel
private theorem s_31017 : BitRUP.StepValid rupClauses rupHints 31017 := by decide +kernel
private theorem s_31018 : BitRUP.StepValid rupClauses rupHints 31018 := by decide +kernel
private theorem s_31019 : BitRUP.StepValid rupClauses rupHints 31019 := by decide +kernel
private theorem s_31020 : BitRUP.StepValid rupClauses rupHints 31020 := by decide +kernel
private theorem s_31021 : BitRUP.StepValid rupClauses rupHints 31021 := by decide +kernel
private theorem s_31022 : BitRUP.StepValid rupClauses rupHints 31022 := by decide +kernel
private theorem s_31023 : BitRUP.StepValid rupClauses rupHints 31023 := by decide +kernel
private theorem s_31024 : BitRUP.StepValid rupClauses rupHints 31024 := by decide +kernel
private theorem s_31025 : BitRUP.StepValid rupClauses rupHints 31025 := by decide +kernel
private theorem s_31026 : BitRUP.StepValid rupClauses rupHints 31026 := by decide +kernel
private theorem s_31027 : BitRUP.StepValid rupClauses rupHints 31027 := by decide +kernel
private theorem s_31028 : BitRUP.StepValid rupClauses rupHints 31028 := by decide +kernel
private theorem s_31029 : BitRUP.StepValid rupClauses rupHints 31029 := by decide +kernel
private theorem s_31030 : BitRUP.StepValid rupClauses rupHints 31030 := by decide +kernel
private theorem s_31031 : BitRUP.StepValid rupClauses rupHints 31031 := by decide +kernel
private theorem s_31032 : BitRUP.StepValid rupClauses rupHints 31032 := by decide +kernel
private theorem s_31033 : BitRUP.StepValid rupClauses rupHints 31033 := by decide +kernel
private theorem s_31034 : BitRUP.StepValid rupClauses rupHints 31034 := by decide +kernel
private theorem s_31035 : BitRUP.StepValid rupClauses rupHints 31035 := by decide +kernel
private theorem s_31036 : BitRUP.StepValid rupClauses rupHints 31036 := by decide +kernel
private theorem s_31037 : BitRUP.StepValid rupClauses rupHints 31037 := by decide +kernel
private theorem s_31038 : BitRUP.StepValid rupClauses rupHints 31038 := by decide +kernel
private theorem s_31039 : BitRUP.StepValid rupClauses rupHints 31039 := by decide +kernel
theorem sBlock121 : ∀ k < 35, BitRUP.StepValid rupClauses rupHints (31005 + k) := fun k hk =>
  ((Fin.cases s_31005 (Fin.cases s_31006 (Fin.cases s_31007 (Fin.cases s_31008 (Fin.cases s_31009 (Fin.cases s_31010 (Fin.cases s_31011 (Fin.cases s_31012 (Fin.cases s_31013 (Fin.cases s_31014 (Fin.cases s_31015 (Fin.cases s_31016 (Fin.cases s_31017 (Fin.cases s_31018 (Fin.cases s_31019 (Fin.cases s_31020 (Fin.cases s_31021 (Fin.cases s_31022 (Fin.cases s_31023 (Fin.cases s_31024 (Fin.cases s_31025 (Fin.cases s_31026 (Fin.cases s_31027 (Fin.cases s_31028 (Fin.cases s_31029 (Fin.cases s_31030 (Fin.cases s_31031 (Fin.cases s_31032 (Fin.cases s_31033 (Fin.cases s_31034 (Fin.cases s_31035 (Fin.cases s_31036 (Fin.cases s_31037 (Fin.cases s_31038 (Fin.cases s_31039 (fun k => Fin.elim0 k)))))))))))))))))))))))))))))))))))) : ∀ k : Fin 35, BitRUP.StepValid rupClauses rupHints (31005 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_10_t12
