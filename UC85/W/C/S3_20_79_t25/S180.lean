import UC85.W.C.S3_20_79_t25.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_20_79_t25
open Modulus40 UC85.W.U

private theorem s_55015 : BitRUP.StepValid rupClauses rupHints 55015 := by decide +kernel
private theorem s_55016 : BitRUP.StepValid rupClauses rupHints 55016 := by decide +kernel
private theorem s_55017 : BitRUP.StepValid rupClauses rupHints 55017 := by decide +kernel
private theorem s_55018 : BitRUP.StepValid rupClauses rupHints 55018 := by decide +kernel
private theorem s_55019 : BitRUP.StepValid rupClauses rupHints 55019 := by decide +kernel
private theorem s_55020 : BitRUP.StepValid rupClauses rupHints 55020 := by decide +kernel
private theorem s_55021 : BitRUP.StepValid rupClauses rupHints 55021 := by decide +kernel
private theorem s_55022 : BitRUP.StepValid rupClauses rupHints 55022 := by decide +kernel
private theorem s_55023 : BitRUP.StepValid rupClauses rupHints 55023 := by decide +kernel
private theorem s_55024 : BitRUP.StepValid rupClauses rupHints 55024 := by decide +kernel
private theorem s_55025 : BitRUP.StepValid rupClauses rupHints 55025 := by decide +kernel
private theorem s_55026 : BitRUP.StepValid rupClauses rupHints 55026 := by decide +kernel
private theorem s_55027 : BitRUP.StepValid rupClauses rupHints 55027 := by decide +kernel
private theorem s_55028 : BitRUP.StepValid rupClauses rupHints 55028 := by decide +kernel
private theorem s_55029 : BitRUP.StepValid rupClauses rupHints 55029 := by decide +kernel
private theorem s_55030 : BitRUP.StepValid rupClauses rupHints 55030 := by decide +kernel
private theorem s_55031 : BitRUP.StepValid rupClauses rupHints 55031 := by decide +kernel
private theorem s_55032 : BitRUP.StepValid rupClauses rupHints 55032 := by decide +kernel
private theorem s_55033 : BitRUP.StepValid rupClauses rupHints 55033 := by decide +kernel
private theorem s_55034 : BitRUP.StepValid rupClauses rupHints 55034 := by decide +kernel
private theorem s_55035 : BitRUP.StepValid rupClauses rupHints 55035 := by decide +kernel
private theorem s_55036 : BitRUP.StepValid rupClauses rupHints 55036 := by decide +kernel
private theorem s_55037 : BitRUP.StepValid rupClauses rupHints 55037 := by decide +kernel
private theorem s_55038 : BitRUP.StepValid rupClauses rupHints 55038 := by decide +kernel
private theorem s_55039 : BitRUP.StepValid rupClauses rupHints 55039 := by decide +kernel
private theorem s_55040 : BitRUP.StepValid rupClauses rupHints 55040 := by decide +kernel
private theorem s_55041 : BitRUP.StepValid rupClauses rupHints 55041 := by decide +kernel
private theorem s_55042 : BitRUP.StepValid rupClauses rupHints 55042 := by decide +kernel
private theorem s_55043 : BitRUP.StepValid rupClauses rupHints 55043 := by decide +kernel
private theorem s_55044 : BitRUP.StepValid rupClauses rupHints 55044 := by decide +kernel
private theorem s_55045 : BitRUP.StepValid rupClauses rupHints 55045 := by decide +kernel
private theorem s_55046 : BitRUP.StepValid rupClauses rupHints 55046 := by decide +kernel
theorem sBlock180 : ∀ k < 32, BitRUP.StepValid rupClauses rupHints (55015 + k) := fun k hk =>
  ((Fin.cases s_55015 (Fin.cases s_55016 (Fin.cases s_55017 (Fin.cases s_55018 (Fin.cases s_55019 (Fin.cases s_55020 (Fin.cases s_55021 (Fin.cases s_55022 (Fin.cases s_55023 (Fin.cases s_55024 (Fin.cases s_55025 (Fin.cases s_55026 (Fin.cases s_55027 (Fin.cases s_55028 (Fin.cases s_55029 (Fin.cases s_55030 (Fin.cases s_55031 (Fin.cases s_55032 (Fin.cases s_55033 (Fin.cases s_55034 (Fin.cases s_55035 (Fin.cases s_55036 (Fin.cases s_55037 (Fin.cases s_55038 (Fin.cases s_55039 (Fin.cases s_55040 (Fin.cases s_55041 (Fin.cases s_55042 (Fin.cases s_55043 (Fin.cases s_55044 (Fin.cases s_55045 (Fin.cases s_55046 (fun k => Fin.elim0 k))))))))))))))))))))))))))))))))) : ∀ k : Fin 32, BitRUP.StepValid rupClauses rupHints (55015 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_20_79_t25
