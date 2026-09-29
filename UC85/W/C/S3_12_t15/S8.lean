import UC85.W.C.S3_12_t15.Tab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_12_t15
open Modulus40 UC85.W.U

private theorem s_1985 : BitRUP.StepValid rupClauses rupHints 1985 := by decide +kernel
private theorem s_1986 : BitRUP.StepValid rupClauses rupHints 1986 := by decide +kernel
private theorem s_1987 : BitRUP.StepValid rupClauses rupHints 1987 := by decide +kernel
private theorem s_1988 : BitRUP.StepValid rupClauses rupHints 1988 := by decide +kernel
private theorem s_1989 : BitRUP.StepValid rupClauses rupHints 1989 := by decide +kernel
private theorem s_1990 : BitRUP.StepValid rupClauses rupHints 1990 := by decide +kernel
private theorem s_1991 : BitRUP.StepValid rupClauses rupHints 1991 := by decide +kernel
private theorem s_1992 : BitRUP.StepValid rupClauses rupHints 1992 := by decide +kernel
private theorem s_1993 : BitRUP.StepValid rupClauses rupHints 1993 := by decide +kernel
private theorem s_1994 : BitRUP.StepValid rupClauses rupHints 1994 := by decide +kernel
private theorem s_1995 : BitRUP.StepValid rupClauses rupHints 1995 := by decide +kernel
private theorem s_1996 : BitRUP.StepValid rupClauses rupHints 1996 := by decide +kernel
private theorem s_1997 : BitRUP.StepValid rupClauses rupHints 1997 := by decide +kernel
private theorem s_1998 : BitRUP.StepValid rupClauses rupHints 1998 := by decide +kernel
private theorem s_1999 : BitRUP.StepValid rupClauses rupHints 1999 := by decide +kernel
private theorem s_2000 : BitRUP.StepValid rupClauses rupHints 2000 := by decide +kernel
private theorem s_2001 : BitRUP.StepValid rupClauses rupHints 2001 := by decide +kernel
private theorem s_2002 : BitRUP.StepValid rupClauses rupHints 2002 := by decide +kernel
private theorem s_2003 : BitRUP.StepValid rupClauses rupHints 2003 := by decide +kernel
private theorem s_2004 : BitRUP.StepValid rupClauses rupHints 2004 := by decide +kernel
private theorem s_2005 : BitRUP.StepValid rupClauses rupHints 2005 := by decide +kernel
private theorem s_2006 : BitRUP.StepValid rupClauses rupHints 2006 := by decide +kernel
private theorem s_2007 : BitRUP.StepValid rupClauses rupHints 2007 := by decide +kernel
private theorem s_2008 : BitRUP.StepValid rupClauses rupHints 2008 := by decide +kernel
private theorem s_2009 : BitRUP.StepValid rupClauses rupHints 2009 := by decide +kernel
private theorem s_2010 : BitRUP.StepValid rupClauses rupHints 2010 := by decide +kernel
private theorem s_2011 : BitRUP.StepValid rupClauses rupHints 2011 := by decide +kernel
private theorem s_2012 : BitRUP.StepValid rupClauses rupHints 2012 := by decide +kernel
private theorem s_2013 : BitRUP.StepValid rupClauses rupHints 2013 := by decide +kernel
private theorem s_2014 : BitRUP.StepValid rupClauses rupHints 2014 := by decide +kernel
private theorem s_2015 : BitRUP.StepValid rupClauses rupHints 2015 := by decide +kernel
private theorem s_2016 : BitRUP.StepValid rupClauses rupHints 2016 := by decide +kernel
theorem sBlock8 : ∀ k < 32, BitRUP.StepValid rupClauses rupHints (1985 + k) := fun k hk =>
  ((Fin.cases s_1985 (Fin.cases s_1986 (Fin.cases s_1987 (Fin.cases s_1988 (Fin.cases s_1989 (Fin.cases s_1990 (Fin.cases s_1991 (Fin.cases s_1992 (Fin.cases s_1993 (Fin.cases s_1994 (Fin.cases s_1995 (Fin.cases s_1996 (Fin.cases s_1997 (Fin.cases s_1998 (Fin.cases s_1999 (Fin.cases s_2000 (Fin.cases s_2001 (Fin.cases s_2002 (Fin.cases s_2003 (Fin.cases s_2004 (Fin.cases s_2005 (Fin.cases s_2006 (Fin.cases s_2007 (Fin.cases s_2008 (Fin.cases s_2009 (Fin.cases s_2010 (Fin.cases s_2011 (Fin.cases s_2012 (Fin.cases s_2013 (Fin.cases s_2014 (Fin.cases s_2015 (Fin.cases s_2016 (fun k => Fin.elim0 k))))))))))))))))))))))))))))))))) : ∀ k : Fin 32, BitRUP.StepValid rupClauses rupHints (1985 + k.val)) ⟨k, hk⟩

end UC85.W.C.S3_12_t15
