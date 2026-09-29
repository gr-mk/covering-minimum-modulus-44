import Mathlib.Tactic.IntervalCases
import UC85.W.U.Rays
import UC85.W.C.S3_4_t0.M
import UC85.W.C.S3_4_t1.M
import UC85.W.C.S3_4_t2.M
import UC85.W.C.S3_4_t3.M
import UC85.W.C.S3_5_t4.M
import UC85.W.C.S3_5_t5.M
import UC85.W.C.S3_6_t6.M
import UC85.W.C.S3_6_t7.M
import UC85.W.C.S3_7_t8.M
import UC85.W.C.S3_8_t9.M
import UC85.W.C.S3_9_t10.M
import UC85.W.C.S3_10_t11.M
import UC85.W.C.S3_10_t12.M
import UC85.W.C.S3_11_t13.M
import UC85.W.C.S3_12_t14.M
import UC85.W.C.S3_12_t15.M
import UC85.W.C.S3_13_t16.M
import UC85.W.C.S3_14_t17.M
import UC85.W.C.S3_15_t18.M
import UC85.W.C.S3_16_t19.M
import UC85.W.C.S3_17_t20.M
import UC85.W.C.S3_18_61_t21.M
import UC85.W.C.S3_18_67_t22.M
import UC85.W.C.S3_19_71_t23.M
import UC85.W.C.S3_19_73_t24.M
import UC85.W.C.S3_20_79_t25.M
import UC85.W.C.S3_20_83_t26.M
import UC85.W.C.S3_21_89_t27.M
import UC85.W.C.S3_21_97_t28.M
import UC85.W.C.S3_21_101_t29.M
import UC85.W.C.S3_21_103_t30.M
import UC85.W.C.S3_21_107_t31.M
import UC85.W.C.S3_21_109_t32.M
import UC85.W.C.S3_21_113_t33.M
import UC85.W.C.S3_21_127_t34.M
import UC85.W.C.S3_21_131_t35.M
import UC85.W.C.S3_21_137_t36.M
import UC85.W.C.S3_21_139_t37.M
import UC85.W.C.S3_21_149_t38.M
import UC85.W.C.S3_21_151_t39.M
import UC85.W.C.S3_21_157_t40.M
import UC85.W.C.S3_21_163_t41.M
import UC85.W.C.S3_21_167_t42.M
import UC85.W.C.S3_21_173_t43.M
import UC85.W.C.S3_21_179_t44.M
import UC85.W.C.S3_21_181_t45.M
import UC85.W.C.S3_21_191_t46.M
import UC85.W.C.S3_21_193_t47.M
import UC85.W.C.S3_21_197_t48.M
import UC85.W.C.S3_21_199_t49.M
import UC85.W.C.S3_21_211_t50.M
import UC85.W.C.G1.M
import UC85.W.C.G3_a0.M
import UC85.W.C.G3_a1.M
import UC85.W.C.G3_a2.M
import UC85.W.C.G3_a3.M
import UC85.W.C.G3_a4.M
import UC85.W.C.G3_a5.M
import UC85.W.C.G3_a6.M
import UC85.W.C.G3_a7.M
import UC85.W.C.G3_a8.M
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def Q (z : ℤ) : Prop := (∃ i : Fin 618413, (patterns i).Matches primes z) ∨
  ∃ (i : Fin 618413) (j : Fin 47), (patterns i j).IsRayCenter z
theorem qf {z : ℤ} {i : ℕ} (hi : i < 618413) (h : (patExt i).Matches primes z) : Q z := Or.inl ⟨⟨i, hi⟩, h⟩
theorem qc {z : ℤ} (h : ∃ j, ∃ r ∈ (lds j).rays, z = r.center) : Q z := Or.inr (center_of z h)
theorem remap_lt {lo mid off i : ℕ} (h : i < mid) : remap lo mid off i = lo + i := if_pos h
theorem remap_ge {lo mid off i : ℕ} (h : ¬ i < mid) : remap lo mid off i = off + (i - mid) := if_neg h
theorem mk_fam (t : Fin 47 → ℕ) (lo mid off count i : ℕ) :
    (mkEnv t lo mid off count).fam i = patExt (remap lo mid off i) := by
  funext j; rfl
theorem mk_target (n lo mid off count : ℕ) :
    (mkEnv (fun j => famIdxExt n j) lo mid off count).target = patExt n := by
  funext j; rfl

theorem zero_matches (z : ℤ) : C.G1.E.target.Matches primes z := by
  intro j
  have h0 : C.G1.E.target j = .fixed 0 0 := by fin_cases j <;> rfl
  rw [h0, Coordinate.matches_fixed]
  simp [Congruence.Covers]

theorem h1 (z : ℤ) : Q z ∨ ∃ t < 51, (patExt (618413 + t)).Matches primes z := by
  have hz := zero_matches z
  have hres := C.G1.check z hz
  rw [show C.G1.E = mkEnv (fun _ => 0) 0 40 618413 91 from rfl] at hres
  simp only [mk_fam] at hres
  rcases hres with ⟨i, hi, hm⟩ | hc
  · by_cases h : i < 40
    · rw [remap_lt h] at hm; exact Or.inl (qf (i := i) (by omega) (by simpa using hm))
    · rw [remap_ge h] at hm; exact Or.inr ⟨i - 40, by omega, hm⟩
  · exact Or.inl (qc hc)

theorem h2a : ∀ t < 4, ∀ z, (patExt (618413 + t)).Matches primes z → Q z ∨ ∃ a < 9, (patExt (618464 + a)).Matches primes z := by
  intro t ht z hz
  interval_cases t
  · have hz' : C.S3_4_t0.E.target.Matches primes z := by
      rw [show C.S3_4_t0.E = mkEnv (fun j => famIdxExt 618413 j) 0 618413 618464 618422 from rfl, mk_target]; exact hz
    have hres := C.S3_4_t0.check z hz'
    rw [show C.S3_4_t0.E = mkEnv (fun j => famIdxExt 618413 j) 0 618413 618464 618422 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · by_cases h : i < 618413
      · rw [remap_lt h] at hm; exact Or.inl (qf (i := i) (by omega) (by simpa using hm))
      · rw [remap_ge h] at hm; exact Or.inr ⟨i - 618413, by omega, hm⟩
    · exact Or.inl (qc hc)
  · have hz' : C.S3_4_t1.E.target.Matches primes z := by
      rw [show C.S3_4_t1.E = mkEnv (fun j => famIdxExt 618414 j) 0 618413 618464 618422 from rfl, mk_target]; exact hz
    have hres := C.S3_4_t1.check z hz'
    rw [show C.S3_4_t1.E = mkEnv (fun j => famIdxExt 618414 j) 0 618413 618464 618422 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · by_cases h : i < 618413
      · rw [remap_lt h] at hm; exact Or.inl (qf (i := i) (by omega) (by simpa using hm))
      · rw [remap_ge h] at hm; exact Or.inr ⟨i - 618413, by omega, hm⟩
    · exact Or.inl (qc hc)
  · have hz' : C.S3_4_t2.E.target.Matches primes z := by
      rw [show C.S3_4_t2.E = mkEnv (fun j => famIdxExt 618415 j) 0 618413 618464 618422 from rfl, mk_target]; exact hz
    have hres := C.S3_4_t2.check z hz'
    rw [show C.S3_4_t2.E = mkEnv (fun j => famIdxExt 618415 j) 0 618413 618464 618422 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · by_cases h : i < 618413
      · rw [remap_lt h] at hm; exact Or.inl (qf (i := i) (by omega) (by simpa using hm))
      · rw [remap_ge h] at hm; exact Or.inr ⟨i - 618413, by omega, hm⟩
    · exact Or.inl (qc hc)
  · have hz' : C.S3_4_t3.E.target.Matches primes z := by
      rw [show C.S3_4_t3.E = mkEnv (fun j => famIdxExt 618416 j) 0 618413 618464 618422 from rfl, mk_target]; exact hz
    have hres := C.S3_4_t3.check z hz'
    rw [show C.S3_4_t3.E = mkEnv (fun j => famIdxExt 618416 j) 0 618413 618464 618422 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · by_cases h : i < 618413
      · rw [remap_lt h] at hm; exact Or.inl (qf (i := i) (by omega) (by simpa using hm))
      · rw [remap_ge h] at hm; exact Or.inr ⟨i - 618413, by omega, hm⟩
    · exact Or.inl (qc hc)

theorem h2b : ∀ t, 4 ≤ t → t < 51 → ∀ z, (patExt (618413 + t)).Matches primes z → Q z := by
  intro t h4 ht z hz
  interval_cases t
  · have hz' : C.S3_5_t4.E.target.Matches primes z := by
      rw [show C.S3_5_t4.E = mkEnv (fun j => famIdxExt 618417 j) 0 154 0 154 from rfl, mk_target]; exact hz
    have hres := C.S3_5_t4.check z hz'
    rw [show C.S3_5_t4.E = mkEnv (fun j => famIdxExt 618417 j) 0 154 0 154 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 154 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_5_t5.E.target.Matches primes z := by
      rw [show C.S3_5_t5.E = mkEnv (fun j => famIdxExt 618418 j) 0 154 0 154 from rfl, mk_target]; exact hz
    have hres := C.S3_5_t5.check z hz'
    rw [show C.S3_5_t5.E = mkEnv (fun j => famIdxExt 618418 j) 0 154 0 154 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 154 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_6_t6.E.target.Matches primes z := by
      rw [show C.S3_6_t6.E = mkEnv (fun j => famIdxExt 618419 j) 0 287 0 287 from rfl, mk_target]; exact hz
    have hres := C.S3_6_t6.check z hz'
    rw [show C.S3_6_t6.E = mkEnv (fun j => famIdxExt 618419 j) 0 287 0 287 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 287 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_6_t7.E.target.Matches primes z := by
      rw [show C.S3_6_t7.E = mkEnv (fun j => famIdxExt 618420 j) 0 287 0 287 from rfl, mk_target]; exact hz
    have hres := C.S3_6_t7.check z hz'
    rw [show C.S3_6_t7.E = mkEnv (fun j => famIdxExt 618420 j) 0 287 0 287 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 287 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_7_t8.E.target.Matches primes z := by
      rw [show C.S3_7_t8.E = mkEnv (fun j => famIdxExt 618421 j) 0 471 0 471 from rfl, mk_target]; exact hz
    have hres := C.S3_7_t8.check z hz'
    rw [show C.S3_7_t8.E = mkEnv (fun j => famIdxExt 618421 j) 0 471 0 471 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 471 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_8_t9.E.target.Matches primes z := by
      rw [show C.S3_8_t9.E = mkEnv (fun j => famIdxExt 618422 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_8_t9.check z hz'
    rw [show C.S3_8_t9.E = mkEnv (fun j => famIdxExt 618422 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_9_t10.E.target.Matches primes z := by
      rw [show C.S3_9_t10.E = mkEnv (fun j => famIdxExt 618423 j) 0 1150 0 1150 from rfl, mk_target]; exact hz
    have hres := C.S3_9_t10.check z hz'
    rw [show C.S3_9_t10.E = mkEnv (fun j => famIdxExt 618423 j) 0 1150 0 1150 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 1150 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_10_t11.E.target.Matches primes z := by
      rw [show C.S3_10_t11.E = mkEnv (fun j => famIdxExt 618424 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_10_t11.check z hz'
    rw [show C.S3_10_t11.E = mkEnv (fun j => famIdxExt 618424 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_10_t12.E.target.Matches primes z := by
      rw [show C.S3_10_t12.E = mkEnv (fun j => famIdxExt 618425 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_10_t12.check z hz'
    rw [show C.S3_10_t12.E = mkEnv (fun j => famIdxExt 618425 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_11_t13.E.target.Matches primes z := by
      rw [show C.S3_11_t13.E = mkEnv (fun j => famIdxExt 618426 j) 0 3312 0 3312 from rfl, mk_target]; exact hz
    have hres := C.S3_11_t13.check z hz'
    rw [show C.S3_11_t13.E = mkEnv (fun j => famIdxExt 618426 j) 0 3312 0 3312 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 3312 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_12_t14.E.target.Matches primes z := by
      rw [show C.S3_12_t14.E = mkEnv (fun j => famIdxExt 618427 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_12_t14.check z hz'
    rw [show C.S3_12_t14.E = mkEnv (fun j => famIdxExt 618427 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_12_t15.E.target.Matches primes z := by
      rw [show C.S3_12_t15.E = mkEnv (fun j => famIdxExt 618428 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_12_t15.check z hz'
    rw [show C.S3_12_t15.E = mkEnv (fun j => famIdxExt 618428 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_13_t16.E.target.Matches primes z := by
      rw [show C.S3_13_t16.E = mkEnv (fun j => famIdxExt 618429 j) 0 7563 0 7563 from rfl, mk_target]; exact hz
    have hres := C.S3_13_t16.check z hz'
    rw [show C.S3_13_t16.E = mkEnv (fun j => famIdxExt 618429 j) 0 7563 0 7563 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 7563 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_14_t17.E.target.Matches primes z := by
      rw [show C.S3_14_t17.E = mkEnv (fun j => famIdxExt 618430 j) 0 11868 0 11868 from rfl, mk_target]; exact hz
    have hres := C.S3_14_t17.check z hz'
    rw [show C.S3_14_t17.E = mkEnv (fun j => famIdxExt 618430 j) 0 11868 0 11868 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 11868 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_15_t18.E.target.Matches primes z := by
      rw [show C.S3_15_t18.E = mkEnv (fun j => famIdxExt 618431 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_15_t18.check z hz'
    rw [show C.S3_15_t18.E = mkEnv (fun j => famIdxExt 618431 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_16_t19.E.target.Matches primes z := by
      rw [show C.S3_16_t19.E = mkEnv (fun j => famIdxExt 618432 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_16_t19.check z hz'
    rw [show C.S3_16_t19.E = mkEnv (fun j => famIdxExt 618432 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_17_t20.E.target.Matches primes z := by
      rw [show C.S3_17_t20.E = mkEnv (fun j => famIdxExt 618433 j) 0 33136 0 33136 from rfl, mk_target]; exact hz
    have hres := C.S3_17_t20.check z hz'
    rw [show C.S3_17_t20.E = mkEnv (fun j => famIdxExt 618433 j) 0 33136 0 33136 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 33136 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_18_61_t21.E.target.Matches primes z := by
      rw [show C.S3_18_61_t21.E = mkEnv (fun j => famIdxExt 618434 j) 0 61731 0 61731 from rfl, mk_target]; exact hz
    have hres := C.S3_18_61_t21.check z hz'
    rw [show C.S3_18_61_t21.E = mkEnv (fun j => famIdxExt 618434 j) 0 61731 0 61731 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 61731 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_18_67_t22.E.target.Matches primes z := by
      rw [show C.S3_18_67_t22.E = mkEnv (fun j => famIdxExt 618435 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_18_67_t22.check z hz'
    rw [show C.S3_18_67_t22.E = mkEnv (fun j => famIdxExt 618435 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_19_71_t23.E.target.Matches primes z := by
      rw [show C.S3_19_71_t23.E = mkEnv (fun j => famIdxExt 618436 j) 0 188182 0 188182 from rfl, mk_target]; exact hz
    have hres := C.S3_19_71_t23.check z hz'
    rw [show C.S3_19_71_t23.E = mkEnv (fun j => famIdxExt 618436 j) 0 188182 0 188182 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 188182 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_19_73_t24.E.target.Matches primes z := by
      rw [show C.S3_19_73_t24.E = mkEnv (fun j => famIdxExt 618437 j) 0 271292 0 271292 from rfl, mk_target]; exact hz
    have hres := C.S3_19_73_t24.check z hz'
    rw [show C.S3_19_73_t24.E = mkEnv (fun j => famIdxExt 618437 j) 0 271292 0 271292 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 271292 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_20_79_t25.E.target.Matches primes z := by
      rw [show C.S3_20_79_t25.E = mkEnv (fun j => famIdxExt 618438 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_20_79_t25.check z hz'
    rw [show C.S3_20_79_t25.E = mkEnv (fun j => famIdxExt 618438 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_20_83_t26.E.target.Matches primes z := by
      rw [show C.S3_20_83_t26.E = mkEnv (fun j => famIdxExt 618439 j) 0 360138 0 360138 from rfl, mk_target]; exact hz
    have hres := C.S3_20_83_t26.check z hz'
    rw [show C.S3_20_83_t26.E = mkEnv (fun j => famIdxExt 618439 j) 0 360138 0 360138 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 360138 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_89_t27.E.target.Matches primes z := by
      rw [show C.S3_21_89_t27.E = mkEnv (fun j => famIdxExt 618440 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_89_t27.check z hz'
    rw [show C.S3_21_89_t27.E = mkEnv (fun j => famIdxExt 618440 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_97_t28.E.target.Matches primes z := by
      rw [show C.S3_21_97_t28.E = mkEnv (fun j => famIdxExt 618441 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_97_t28.check z hz'
    rw [show C.S3_21_97_t28.E = mkEnv (fun j => famIdxExt 618441 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_101_t29.E.target.Matches primes z := by
      rw [show C.S3_21_101_t29.E = mkEnv (fun j => famIdxExt 618442 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_101_t29.check z hz'
    rw [show C.S3_21_101_t29.E = mkEnv (fun j => famIdxExt 618442 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_103_t30.E.target.Matches primes z := by
      rw [show C.S3_21_103_t30.E = mkEnv (fun j => famIdxExt 618443 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_103_t30.check z hz'
    rw [show C.S3_21_103_t30.E = mkEnv (fun j => famIdxExt 618443 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_107_t31.E.target.Matches primes z := by
      rw [show C.S3_21_107_t31.E = mkEnv (fun j => famIdxExt 618444 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_107_t31.check z hz'
    rw [show C.S3_21_107_t31.E = mkEnv (fun j => famIdxExt 618444 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_109_t32.E.target.Matches primes z := by
      rw [show C.S3_21_109_t32.E = mkEnv (fun j => famIdxExt 618445 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_109_t32.check z hz'
    rw [show C.S3_21_109_t32.E = mkEnv (fun j => famIdxExt 618445 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_113_t33.E.target.Matches primes z := by
      rw [show C.S3_21_113_t33.E = mkEnv (fun j => famIdxExt 618446 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_113_t33.check z hz'
    rw [show C.S3_21_113_t33.E = mkEnv (fun j => famIdxExt 618446 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_127_t34.E.target.Matches primes z := by
      rw [show C.S3_21_127_t34.E = mkEnv (fun j => famIdxExt 618447 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_127_t34.check z hz'
    rw [show C.S3_21_127_t34.E = mkEnv (fun j => famIdxExt 618447 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_131_t35.E.target.Matches primes z := by
      rw [show C.S3_21_131_t35.E = mkEnv (fun j => famIdxExt 618448 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_131_t35.check z hz'
    rw [show C.S3_21_131_t35.E = mkEnv (fun j => famIdxExt 618448 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_137_t36.E.target.Matches primes z := by
      rw [show C.S3_21_137_t36.E = mkEnv (fun j => famIdxExt 618449 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_137_t36.check z hz'
    rw [show C.S3_21_137_t36.E = mkEnv (fun j => famIdxExt 618449 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_139_t37.E.target.Matches primes z := by
      rw [show C.S3_21_139_t37.E = mkEnv (fun j => famIdxExt 618450 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_139_t37.check z hz'
    rw [show C.S3_21_139_t37.E = mkEnv (fun j => famIdxExt 618450 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_149_t38.E.target.Matches primes z := by
      rw [show C.S3_21_149_t38.E = mkEnv (fun j => famIdxExt 618451 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_149_t38.check z hz'
    rw [show C.S3_21_149_t38.E = mkEnv (fun j => famIdxExt 618451 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_151_t39.E.target.Matches primes z := by
      rw [show C.S3_21_151_t39.E = mkEnv (fun j => famIdxExt 618452 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_151_t39.check z hz'
    rw [show C.S3_21_151_t39.E = mkEnv (fun j => famIdxExt 618452 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_157_t40.E.target.Matches primes z := by
      rw [show C.S3_21_157_t40.E = mkEnv (fun j => famIdxExt 618453 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_157_t40.check z hz'
    rw [show C.S3_21_157_t40.E = mkEnv (fun j => famIdxExt 618453 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_163_t41.E.target.Matches primes z := by
      rw [show C.S3_21_163_t41.E = mkEnv (fun j => famIdxExt 618454 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_163_t41.check z hz'
    rw [show C.S3_21_163_t41.E = mkEnv (fun j => famIdxExt 618454 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_167_t42.E.target.Matches primes z := by
      rw [show C.S3_21_167_t42.E = mkEnv (fun j => famIdxExt 618455 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_167_t42.check z hz'
    rw [show C.S3_21_167_t42.E = mkEnv (fun j => famIdxExt 618455 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_173_t43.E.target.Matches primes z := by
      rw [show C.S3_21_173_t43.E = mkEnv (fun j => famIdxExt 618456 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_173_t43.check z hz'
    rw [show C.S3_21_173_t43.E = mkEnv (fun j => famIdxExt 618456 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_179_t44.E.target.Matches primes z := by
      rw [show C.S3_21_179_t44.E = mkEnv (fun j => famIdxExt 618457 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_179_t44.check z hz'
    rw [show C.S3_21_179_t44.E = mkEnv (fun j => famIdxExt 618457 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_181_t45.E.target.Matches primes z := by
      rw [show C.S3_21_181_t45.E = mkEnv (fun j => famIdxExt 618458 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_181_t45.check z hz'
    rw [show C.S3_21_181_t45.E = mkEnv (fun j => famIdxExt 618458 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_191_t46.E.target.Matches primes z := by
      rw [show C.S3_21_191_t46.E = mkEnv (fun j => famIdxExt 618459 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_191_t46.check z hz'
    rw [show C.S3_21_191_t46.E = mkEnv (fun j => famIdxExt 618459 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_193_t47.E.target.Matches primes z := by
      rw [show C.S3_21_193_t47.E = mkEnv (fun j => famIdxExt 618460 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_193_t47.check z hz'
    rw [show C.S3_21_193_t47.E = mkEnv (fun j => famIdxExt 618460 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_197_t48.E.target.Matches primes z := by
      rw [show C.S3_21_197_t48.E = mkEnv (fun j => famIdxExt 618461 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_197_t48.check z hz'
    rw [show C.S3_21_197_t48.E = mkEnv (fun j => famIdxExt 618461 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_199_t49.E.target.Matches primes z := by
      rw [show C.S3_21_199_t49.E = mkEnv (fun j => famIdxExt 618462 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_199_t49.check z hz'
    rw [show C.S3_21_199_t49.E = mkEnv (fun j => famIdxExt 618462 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc
  · have hz' : C.S3_21_211_t50.E.target.Matches primes z := by
      rw [show C.S3_21_211_t50.E = mkEnv (fun j => famIdxExt 618463 j) 0 618413 0 618413 from rfl, mk_target]; exact hz
    have hres := C.S3_21_211_t50.check z hz'
    rw [show C.S3_21_211_t50.E = mkEnv (fun j => famIdxExt 618463 j) 0 618413 0 618413 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · have h : i < 618413 := hi
      rw [remap_lt h] at hm; exact qf (i := i) (by omega) (by simpa using hm)
    · exact qc hc

theorem h3 : ∀ a < 9, ∀ z, (patExt (618464 + a)).Matches primes z → Q z ∨ ∃ t, 4 ≤ t ∧ t < 51 ∧ (patExt (618413 + t)).Matches primes z := by
  intro a ha z hz
  interval_cases a
  · have hz' : C.G3_a0.E.target.Matches primes z := by
      rw [show C.G3_a0.E = mkEnv (fun j => famIdxExt 618464 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a0.check z hz'
    rw [show C.G3_a0.E = mkEnv (fun j => famIdxExt 618464 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a1.E.target.Matches primes z := by
      rw [show C.G3_a1.E = mkEnv (fun j => famIdxExt 618465 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a1.check z hz'
    rw [show C.G3_a1.E = mkEnv (fun j => famIdxExt 618465 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a2.E.target.Matches primes z := by
      rw [show C.G3_a2.E = mkEnv (fun j => famIdxExt 618466 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a2.check z hz'
    rw [show C.G3_a2.E = mkEnv (fun j => famIdxExt 618466 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a3.E.target.Matches primes z := by
      rw [show C.G3_a3.E = mkEnv (fun j => famIdxExt 618467 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a3.check z hz'
    rw [show C.G3_a3.E = mkEnv (fun j => famIdxExt 618467 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a4.E.target.Matches primes z := by
      rw [show C.G3_a4.E = mkEnv (fun j => famIdxExt 618468 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a4.check z hz'
    rw [show C.G3_a4.E = mkEnv (fun j => famIdxExt 618468 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a5.E.target.Matches primes z := by
      rw [show C.G3_a5.E = mkEnv (fun j => famIdxExt 618469 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a5.check z hz'
    rw [show C.G3_a5.E = mkEnv (fun j => famIdxExt 618469 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a6.E.target.Matches primes z := by
      rw [show C.G3_a6.E = mkEnv (fun j => famIdxExt 618470 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a6.check z hz'
    rw [show C.G3_a6.E = mkEnv (fun j => famIdxExt 618470 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a7.E.target.Matches primes z := by
      rw [show C.G3_a7.E = mkEnv (fun j => famIdxExt 618471 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a7.check z hz'
    rw [show C.G3_a7.E = mkEnv (fun j => famIdxExt 618471 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)
  · have hz' : C.G3_a8.E.target.Matches primes z := by
      rw [show C.G3_a8.E = mkEnv (fun j => famIdxExt 618472 j) 0 0 618417 47 from rfl, mk_target]; exact hz
    have hres := C.G3_a8.check z hz'
    rw [show C.G3_a8.E = mkEnv (fun j => famIdxExt 618472 j) 0 0 618417 47 from rfl] at hres
    simp only [mk_fam] at hres
    rcases hres with ⟨i, hi, hm⟩ | hc
    · rw [remap_ge (Nat.not_lt_zero i)] at hm
      exact Or.inr ⟨4 + i, by omega, by omega,
        by rwa [show 618413 + (4 + i) = 618417 + (i - 0) by omega]⟩
    · exact Or.inl (qc hc)

/-- MainReduction's `hcover` for UC85: every integer is matched by a family or is a ray centre. -/
theorem hcover_all : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
    ∃ i j, (patterns i j).IsRayCenter z :=
  section_glue Q (fun t z => (patExt (618413 + t)).Matches primes z) (fun a z => (patExt (618464 + a)).Matches primes z)
    4 51 9 h1 h2a h2b h3

end UC85.W.U
