import UC85.W.U.Env
import UC85.W.C.S3_6_t7.clauseAtD0
import UC85.W.C.S3_6_t7.hintAtD0
import UC85.W.C.S3_6_t7.originAtD0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_6_t7
open Modulus40 UC85.W.U

def clauseAt (i : ℕ) : ℕ :=
  (if i < 128 then (if i < 64 then (clauseAtC0[i - 0]?.getD 0) else (clauseAtC1[i - 64]?.getD 0)) else (if i < 192 then (clauseAtC2[i - 128]?.getD 0) else (clauseAtC3[i - 192]?.getD 0)))
def hintAt (i : ℕ) : ℕ :=
  (if i < 64 then (hintAtC0[i - 0]?.getD 0) else (hintAtC1[i - 64]?.getD 0))
def originAt (i : ℕ) : ℕ :=
  (if i < 64 then (originAtC0[i - 0]?.getD 0) else (if i < 128 then (originAtC1[i - 64]?.getD 0) else 0))
def rupClauses (i : ℕ) : RUP.Clause := unpackClause (clauseAt i)
def rupHints (i : ℕ) : List ℕ := unpackHints20 (hintAt (i - 171))
def origin (i : ℕ) : Origin 47 := decodeOrigin 47 (originAt i)
def E : Env 47 := mkEnv (fun j => famIdxExt 618420 j) 0 287 0 287

theorem tgt_ok : ∀ j, E.tIdx j < (E.ld j).coordinates.length := by decide +kernel
theorem final_ok : rupClauses 244 = [] := by decide +kernel

end UC85.W.C.S3_6_t7
