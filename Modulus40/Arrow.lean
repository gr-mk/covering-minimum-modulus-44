import Modulus40.Basic

/-!
# Finite termination of Nielsen's arrows

A finite family of distinct moduli fills any sufficiently deep prime-power
congruence class. The auxiliary number need not be prime: powers of a fixed
fresh prime allow different arrow caps to be distinguished by valuation.
-/

namespace Modulus40

/-- The `i`th congruence used to terminate an arrow at depth `n`.
The residue formula avoids a separate Chinese remainder theorem invocation. -/
def arrowCapClass (q n p i : ℕ) (center : ℤ) : Congruence where
  modulus := q ^ (n - i) * p
  residue := center + (q ^ n : ℕ) * (i : ℤ)

/-- The finite cap consists of one class for every residue modulo the auxiliary number. -/
def arrowCap (q n p : ℕ) (center : ℤ) : List Congruence :=
  (List.range p).map fun i => arrowCapClass q n p i center

/-- The cap fills the entire final hole, including its negative integers. -/
theorem arrowCap_covers {q n p : ℕ} (hp : 0 < p) (center z : ℤ)
    (hz : Int.ModEq (q ^ n : ℕ) z center) :
    ∃ c ∈ arrowCap q n p center, c.Covers z := by
  have hdiv : (q ^ n : ℤ) ∣ z - center := by
    simpa using Int.modEq_iff_dvd.mp hz.symm
  obtain ⟨t, ht⟩ := hdiv
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hnonneg : 0 ≤ t % (p : ℤ) := Int.emod_nonneg t (ne_of_gt hpz)
  have hlt : t % (p : ℤ) < p := Int.emod_lt_of_pos t hpz
  let i := (t % (p : ℤ)).toNat
  have hi : i < p := by dsimp [i]; omega
  have hieq : (i : ℤ) = t % (p : ℤ) := Int.toNat_of_nonneg hnonneg
  refine ⟨arrowCapClass q n p i center, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  · have hbase := (Int.mod_modEq t (p : ℤ)).mul_left' (c := (q : ℤ) ^ n)
    have hsmall : q ^ (n - i) * p ∣ q ^ n * p :=
      Nat.mul_dvd_mul_right (pow_dvd_pow q (Nat.sub_le n i)) p
    have hsmallz : (q : ℤ) ^ (n - i) * p ∣ (q : ℤ) ^ n * p := by
      exact_mod_cast hsmall
    have h := (hbase.of_dvd hsmallz).add_left center
    have hzform : z = center + (q : ℤ) ^ n * t := by linarith
    simpa [Congruence.Covers, arrowCapClass, Int.ModEq, hieq, hzform] using h.symm

/-- A single cap has pairwise distinct moduli when there are enough levels. -/
theorem arrowCap_distinct {q n p : ℕ} (hq : 1 < q) (hp : 0 < p)
    (hn : p - 1 ≤ n) (center : ℤ) :
    DistinctModuli (arrowCap q n p center) := by
  unfold DistinctModuli arrowCap
  rw [List.map_map]
  apply List.Nodup.map_on _ (List.nodup_range)
  intro i hi j hj heq
  have hi' : i < p := List.mem_range.mp hi
  have hj' : j < p := List.mem_range.mp hj
  change q ^ (n - i) * p = q ^ (n - j) * p at heq
  have hexp : n - i = n - j := by
    apply (pow_right_injective₀ (by omega : 0 < q) (by omega : q ≠ 1))
    exact Nat.eq_of_mul_eq_mul_right hp heq
  omega

/-- The class moduli can all be forced above any chosen power of `q`. -/
theorem arrowCap_modulus_lower_bound {q n p depth : ℕ}
    (hq : 0 < q) (hp : 0 < p) (hn : p - 1 + depth ≤ n)
    (center : ℤ) {c : Congruence} (hc : c ∈ arrowCap q n p center) :
    q ^ depth ≤ c.modulus := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  have hi' : i < p := List.mem_range.mp hi
  have hid : depth ≤ n - i := by omega
  change q ^ depth ≤ q ^ (n - i) * p
  calc
    q ^ depth ≤ q ^ (n - i) := Nat.pow_le_pow_right hq hid
    _ ≤ q ^ (n - i) * p := Nat.le_mul_of_pos_right _ hp

/-- Multiplying a core modulus by a fresh prime power records an unambiguous tag. -/
theorem marker_factorization {P q e k : ℕ} (hP : P.Prime) (hq : ¬ P ∣ q) :
    (q ^ e * P ^ k).factorization P = k := by
  have hq0 : q ≠ 0 := by intro h; subst q; exact hq (dvd_zero P)
  rw [Nat.factorization_mul (pow_ne_zero _ hq0) (pow_ne_zero _ hP.ne_zero)]
  have hn : ¬ P ∣ q ^ e := fun h => hq (hP.dvd_of_dvd_pow h)
  change (q ^ e).factorization P + (P ^ k).factorization P = k
  rw [Nat.factorization_eq_zero_of_not_dvd hn, hP.factorization_pow]
  simp

/-- Every modulus in a tagged cap has exactly its assigned marker exponent. -/
theorem arrowCap_marker_factorization {P q n k : ℕ} (hP : P.Prime)
    (hq : ¬ P ∣ q) (center : ℤ) {c : Congruence}
    (hc : c ∈ arrowCap q n (P ^ k) center) :
    c.modulus.factorization P = k := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  exact marker_factorization hP hq

/-- Caps assigned different tags cannot repeat a modulus, even with different bases. -/
theorem arrowCap_moduli_ne {P q r n m k l : ℕ} (hP : P.Prime)
    (hq : ¬ P ∣ q) (hr : ¬ P ∣ r) (hkl : k ≠ l)
    (a b : ℤ) {c d : Congruence}
    (hc : c ∈ arrowCap q n (P ^ k) a)
    (hd : d ∈ arrowCap r m (P ^ l) b) :
    c.modulus ≠ d.modulus := by
  intro heq
  apply hkl
  rw [← arrowCap_marker_factorization hP hq a hc,
    ← arrowCap_marker_factorization hP hr b hd, heq]

/-- A positively tagged cap never repeats an ordinary modulus free of the marker prime. -/
theorem arrowCap_modulus_ne_core {P q n k core : ℕ} (hP : P.Prime)
    (hq : ¬ P ∣ q) (hk : 0 < k) (hcore : ¬ P ∣ core)
    (center : ℤ) {c : Congruence} (hc : c ∈ arrowCap q n (P ^ k) center) :
    c.modulus ≠ core := by
  intro heq
  have h := arrowCap_marker_factorization hP hq center hc
  rw [heq, Nat.factorization_eq_zero_of_not_dvd hcore] at h
  omega

/-- Six spare levels guarantee the numerical lower bound needed by the paper. -/
theorem arrowCap_modulus_ge40 {q n p : ℕ}
    (hq : 1 < q) (hp : 0 < p) (hn : p - 1 + 6 ≤ n)
    (center : ℤ) {c : Congruence} (hc : c ∈ arrowCap q n p center) :
    40 ≤ c.modulus := by
  have hbound := arrowCap_modulus_lower_bound (by omega : 0 < q) hp hn center hc
  have hpower : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left (by omega) 6
  omega

end Modulus40
