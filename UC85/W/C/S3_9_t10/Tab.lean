import UC85.W.U.Env
import UC85.W.C.S3_9_t10.clauseAtD0
import UC85.W.C.S3_9_t10.hintAtD0
import UC85.W.C.S3_9_t10.originAtD0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_9_t10
open Modulus40 UC85.W.U

def clauseAt (i : ℕ) : ℕ :=
  (if i < 320 then (if i < 128 then (if i < 64 then (clauseAtC0[i - 0]?.getD 0) else (clauseAtC1[i - 64]?.getD 0)) else (if i < 192 then (clauseAtC2[i - 128]?.getD 0) else (if i < 256 then (clauseAtC3[i - 192]?.getD 0) else (clauseAtC4[i - 256]?.getD 0)))) else (if i < 512 then (if i < 384 then (clauseAtC5[i - 320]?.getD 0) else (if i < 448 then (clauseAtC6[i - 384]?.getD 0) else (clauseAtC7[i - 448]?.getD 0))) else (if i < 576 then (clauseAtC8[i - 512]?.getD 0) else (if i < 640 then (clauseAtC9[i - 576]?.getD 0) else (clauseAtC10[i - 640]?.getD 0)))))
def hintAt (i : ℕ) : ℕ :=
  (if i < 128 then (if i < 64 then (hintAtC0[i - 0]?.getD 0) else (hintAtC1[i - 64]?.getD 0)) else (if i < 192 then (hintAtC2[i - 128]?.getD 0) else (hintAtC3[i - 192]?.getD 0)))
def originAt (i : ℕ) : ℕ :=
  (if i < 256 then (if i < 128 then (if i < 64 then (originAtC0[i - 0]?.getD 0) else (originAtC1[i - 64]?.getD 0)) else (if i < 192 then (originAtC2[i - 128]?.getD 0) else (originAtC3[i - 192]?.getD 0))) else (if i < 384 then (if i < 320 then (originAtC4[i - 256]?.getD 0) else (originAtC5[i - 320]?.getD 0)) else (if i < 448 then (originAtC6[i - 384]?.getD 0) else 0)))
def rupClauses (i : ℕ) : RUP.Clause := unpackClause (clauseAt i)
def rupHints (i : ℕ) : List ℕ := unpackHints20 (hintAt (i - 462))
def origin (i : ℕ) : Origin 47 := decodeOrigin 47 (originAt i)
def E : Env 47 := mkEnv (fun j => famIdxExt 618423 j) 0 1150 0 1150

theorem tgt_ok : ∀ j, E.tIdx j < (E.ld j).coordinates.length := by decide +kernel
theorem final_ok : rupClauses 684 = [] := by decide +kernel

end UC85.W.C.S3_9_t10
