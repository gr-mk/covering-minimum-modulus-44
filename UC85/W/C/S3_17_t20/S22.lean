import UC85.W.C.S3_17_t20.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_17_t20
open Modulus40 UC85.W.U

private theorem s_6646 : BitRUP.StepValid rupClauses rupHints 6646 := by decide +kernel
private theorem s_6647 : BitRUP.StepValid rupClauses rupHints 6647 := by decide +kernel
private theorem s_6648 : BitRUP.StepValid rupClauses rupHints 6648 := by decide +kernel
private theorem s_6649 : BitRUP.StepValid rupClauses rupHints 6649 := by decide +kernel
private theorem s_6650 : BitRUP.StepValid rupClauses rupHints 6650 := by decide +kernel
private theorem s_6651 : BitRUP.StepValid rupClauses rupHints 6651 := by decide +kernel
private theorem s_6652 : BitRUP.StepValid rupClauses rupHints 6652 := by decide +kernel
private theorem s_6653 : BitRUP.StepValid rupClauses rupHints 6653 := by decide +kernel
private theorem s_6654 : BitRUP.StepValid rupClauses rupHints 6654 := by decide +kernel
private theorem s_6655 : BitRUP.StepValid rupClauses rupHints 6655 := by decide +kernel
private theorem s_6656 : BitRUP.StepValid rupClauses rupHints 6656 := by decide +kernel
private theorem s_6657 : BitRUP.StepValid rupClauses rupHints 6657 := by decide +kernel
private theorem s_6658 : BitRUP.StepValid rupClauses rupHints 6658 := by decide +kernel
private theorem s_6659 : BitRUP.StepValid rupClauses rupHints 6659 := by decide +kernel
private theorem s_6660 : BitRUP.StepValid rupClauses rupHints 6660 := by decide +kernel
private theorem s_6661 : BitRUP.StepValid rupClauses rupHints 6661 := by decide +kernel
private theorem s_6662 : BitRUP.StepValid rupClauses rupHints 6662 := by decide +kernel
private theorem s_6663 : BitRUP.StepValid rupClauses rupHints 6663 := by decide +kernel
private theorem s_6664 : BitRUP.StepValid rupClauses rupHints 6664 := by decide +kernel
private theorem s_6665 : BitRUP.StepValid rupClauses rupHints 6665 := by decide +kernel
private theorem s_6666 : BitRUP.StepValid rupClauses rupHints 6666 := by decide +kernel
private theorem s_6667 : BitRUP.StepValid rupClauses rupHints 6667 := by decide +kernel
private theorem s_6668 : BitRUP.StepValid rupClauses rupHints 6668 := by decide +kernel
private theorem s_6669 : BitRUP.StepValid rupClauses rupHints 6669 := by decide +kernel
private theorem s_6670 : BitRUP.StepValid rupClauses rupHints 6670 := by decide +kernel
private theorem s_6671 : BitRUP.StepValid rupClauses rupHints 6671 := by decide +kernel
private theorem s_6672 : BitRUP.StepValid rupClauses rupHints 6672 := by decide +kernel
private theorem s_6673 : BitRUP.StepValid rupClauses rupHints 6673 := by decide +kernel
private theorem s_6674 : BitRUP.StepValid rupClauses rupHints 6674 := by decide +kernel
private theorem s_6675 : BitRUP.StepValid rupClauses rupHints 6675 := by decide +kernel
private theorem s_6676 : BitRUP.StepValid rupClauses rupHints 6676 := by decide +kernel
theorem sBlock22 : ∀ k < 31, BitRUP.StepValid rupClauses rupHints (6646 + k) := fun k hk =>
  ((Fin.cases s_6646 (Fin.cases s_6647 (Fin.cases s_6648 (Fin.cases s_6649 (Fin.cases s_6650 (Fin.cases s_6651 (Fin.cases s_6652 (Fin.cases s_6653 (Fin.cases s_6654 (Fin.cases s_6655 (Fin.cases s_6656 (Fin.cases s_6657 (Fin.cases s_6658 (Fin.cases s_6659 (Fin.cases s_6660 (Fin.cases s_6661 (Fin.cases s_6662 (Fin.cases s_6663 (Fin.cases s_6664 (Fin.cases s_6665 (Fin.cases s_6666 (Fin.cases s_6667 (Fin.cases s_6668 (Fin.cases s_6669 (Fin.cases s_6670 (Fin.cases s_6671 (Fin.cases s_6672 (Fin.cases s_6673 (Fin.cases s_6674 (Fin.cases s_6675 (Fin.cases s_6676 (fun k => Fin.elim0 k)))))))))))))))))))))))))))))))) : ∀ k : Fin 31, BitRUP.StepValid rupClauses rupHints (6646 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_17_t20
