import UC85.W.U.Env
import UC85.W.C.S3_12_t15.clauseAtD0
import UC85.W.C.S3_12_t15.hintAtD0
import UC85.W.C.S3_12_t15.originAtD0
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace UC85.W.C.S3_12_t15
open Modulus40 UC85.W.U

def clauseAt (i : ℕ) : ℕ :=
  (if i < 1024 then (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (clauseAtC0[i - 0]?.getD 0) else (clauseAtC1[i - 64]?.getD 0)) else (if i < 192 then (clauseAtC2[i - 128]?.getD 0) else (clauseAtC3[i - 192]?.getD 0))) else (if i < 384 then (if i < 320 then (clauseAtC4[i - 256]?.getD 0) else (clauseAtC5[i - 320]?.getD 0)) else (if i < 448 then (clauseAtC6[i - 384]?.getD 0) else (clauseAtC7[i - 448]?.getD 0)))) else (if i < 768 then (if i < 640 then (if i < 576 then (clauseAtC8[i - 512]?.getD 0) else (clauseAtC9[i - 576]?.getD 0)) else (if i < 704 then (clauseAtC10[i - 640]?.getD 0) else (clauseAtC11[i - 704]?.getD 0))) else (if i < 896 then (if i < 832 then (clauseAtC12[i - 768]?.getD 0) else (clauseAtC13[i - 832]?.getD 0)) else (if i < 960 then (clauseAtC14[i - 896]?.getD 0) else (clauseAtC15[i - 960]?.getD 0))))) else (if i < 1536 then (if i < 1280 then (if i < 1152 then (if i < 1088 then (clauseAtC16[i - 1024]?.getD 0) else (clauseAtC17[i - 1088]?.getD 0)) else (if i < 1216 then (clauseAtC18[i - 1152]?.getD 0) else (clauseAtC19[i - 1216]?.getD 0))) else (if i < 1408 then (if i < 1344 then (clauseAtC20[i - 1280]?.getD 0) else (clauseAtC21[i - 1344]?.getD 0)) else (if i < 1472 then (clauseAtC22[i - 1408]?.getD 0) else (clauseAtC23[i - 1472]?.getD 0)))) else (if i < 1792 then (if i < 1664 then (if i < 1600 then (clauseAtC24[i - 1536]?.getD 0) else (clauseAtC25[i - 1600]?.getD 0)) else (if i < 1728 then (clauseAtC26[i - 1664]?.getD 0) else (clauseAtC27[i - 1728]?.getD 0))) else (if i < 1920 then (if i < 1856 then (clauseAtC28[i - 1792]?.getD 0) else (clauseAtC29[i - 1856]?.getD 0)) else (if i < 1984 then (clauseAtC30[i - 1920]?.getD 0) else (clauseAtC31[i - 1984]?.getD 0))))))
def hintAt (i : ℕ) : ℕ :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (hintAtC0[i - 0]?.getD 0) else (hintAtC1[i - 64]?.getD 0)) else (if i < 192 then (hintAtC2[i - 128]?.getD 0) else (hintAtC3[i - 192]?.getD 0))) else (if i < 384 then (if i < 320 then (hintAtC4[i - 256]?.getD 0) else (hintAtC5[i - 320]?.getD 0)) else (if i < 448 then (hintAtC6[i - 384]?.getD 0) else (hintAtC7[i - 448]?.getD 0)))) else (if i < 768 then (if i < 640 then (if i < 576 then (hintAtC8[i - 512]?.getD 0) else (hintAtC9[i - 576]?.getD 0)) else (if i < 704 then (hintAtC10[i - 640]?.getD 0) else (hintAtC11[i - 704]?.getD 0))) else (if i < 896 then (if i < 832 then (hintAtC12[i - 768]?.getD 0) else (hintAtC13[i - 832]?.getD 0)) else (if i < 960 then (hintAtC14[i - 896]?.getD 0) else (if i < 1024 then (hintAtC15[i - 960]?.getD 0) else (hintAtC16[i - 1024]?.getD 0))))))
def originAt (i : ℕ) : ℕ :=
  (if i < 512 then (if i < 256 then (if i < 128 then (if i < 64 then (originAtC0[i - 0]?.getD 0) else (originAtC1[i - 64]?.getD 0)) else (if i < 192 then (originAtC2[i - 128]?.getD 0) else (originAtC3[i - 192]?.getD 0))) else (if i < 384 then (if i < 320 then (originAtC4[i - 256]?.getD 0) else (originAtC5[i - 320]?.getD 0)) else (if i < 448 then (originAtC6[i - 384]?.getD 0) else (originAtC7[i - 448]?.getD 0)))) else (if i < 768 then (if i < 640 then (if i < 576 then (originAtC8[i - 512]?.getD 0) else (originAtC9[i - 576]?.getD 0)) else (if i < 704 then (originAtC10[i - 640]?.getD 0) else (originAtC11[i - 704]?.getD 0))) else (if i < 896 then (if i < 832 then (originAtC12[i - 768]?.getD 0) else (originAtC13[i - 832]?.getD 0)) else (if i < 960 then (originAtC14[i - 896]?.getD 0) else 0))))
def rupClauses (i : ℕ) : RUP.Clause := unpackClause (clauseAt i)
def rupHints (i : ℕ) : List ℕ := unpackHints20 (hintAt (i - 961))
def origin (i : ℕ) : Origin 47 := decodeOrigin 47 (originAt i)
def E : Env 47 := mkEnv (fun j => famIdxExt 618428 j) 0 618413 0 618413

theorem tgt_ok : ∀ j, E.tIdx j < (E.ld j).coordinates.length := by decide +kernel
theorem final_ok : rupClauses 2016 = [] := by decide +kernel

end UC85.W.C.S3_12_t15
