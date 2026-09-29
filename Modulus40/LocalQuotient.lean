import Modulus40.RaySemantics

/-!
# Finite representatives for prime-power ray predicates

Residues away from all centers are represented modulo a fixed prime power.
Near a center, the first nonzero digit determines every ray predicate with that
center; rays with different centers are already determined by the fixed residue.
-/

namespace Modulus40

/-- Two valid rays with the same prime base and center can match the same
integer only if their nonzero digits agree. -/
theorem ray_digit_eq_of_matches {q first second digit other : ℕ} {center z : ℤ}
    (hq : q.Prime) (hf : 1 ≤ first) (hs : 1 ≤ second)
    (hd : 1 ≤ digit) (hdq : digit < q) (ho : 1 ≤ other) (hoq : other < q)
    (hz : (Ray.mk q first center digit).Matches z)
    (hw : (Ray.mk q second center other).Matches z) : digit = other := by
  obtain ⟨k, hk, hzk⟩ := hz
  obtain ⟨l, hl, hwl⟩ := hw
  have hkp : 1 ≤ k := by change first ≤ k at hk; omega
  have hlp : 1 ≤ l := by change second ≤ l at hl; omega
  have hke := Ray.level_eq_padicVal_add_one hq hd hdq hkp hzk
  have hle := Ray.level_eq_padicVal_add_one hq ho hoq hlp hwl
  have hkl : k = l := by simpa using hke.trans hle.symm
  rw [← hkl] at hwl
  have hzk' : Int.ModEq ((q : ℤ) ^ k) z
      (center + (digit : ℤ) * (q : ℤ) ^ (k - 1)) := by
    simpa [Ray.at, Congruence.Covers, Int.ModEq] using hzk
  have hwk' : Int.ModEq ((q : ℤ) ^ k) z
      (center + (other : ℤ) * (q : ℤ) ^ (k - 1)) := by
    simpa [Ray.at, Congruence.Covers, Int.ModEq] using hwl
  have hdiv := (hzk'.symm.trans hwk').dvd
  have heq : center + (other : ℤ) * (q : ℤ) ^ (k - 1) -
      (center + (digit : ℤ) * (q : ℤ) ^ (k - 1)) =
      ((other : ℤ) - digit) * (q : ℤ) ^ (k - 1) := by ring
  rw [heq] at hdiv
  have hpow : (q : ℤ) ^ k = (q : ℤ) * (q : ℤ) ^ (k - 1) := by
    calc
      (q : ℤ) ^ k = (q : ℤ) ^ ((k - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ' _ _
  rw [hpow] at hdiv
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdiv' := (mul_dvd_mul_iff_right (pow_ne_zero (k - 1) hq0)).mp hdiv
  have hmod : Int.ModEq (q : ℤ) (digit : ℤ) (other : ℤ) :=
    Int.modEq_iff_dvd.mpr hdiv'
  exact (Int.natCast_modEq_iff.mp hmod).eq_of_lt_of_lt hdq hoq

/-- In a deep central residue class, a ray's truth is determined just by its
digit, independently of how deep the first nonzero digit occurs. -/
theorem ray_matches_iff_digit_of_deep_match {q depth first digit other : ℕ}
    {center z : ℤ} (hq : q.Prime) (hf : 1 ≤ first) (hfdepth : first ≤ depth + 1)
    (hd : 1 ≤ digit) (hdq : digit < q) (ho : 1 ≤ other) (hoq : other < q)
    (hz : (Ray.mk q (depth + 1) center digit).Matches z) :
    (Ray.mk q first center other).Matches z ↔ other = digit := by
  constructor
  · intro hw
    exact ray_digit_eq_of_matches hq hf (by omega) ho hoq hd hdq hw hz
  · rintro rfl
    obtain ⟨k, hk, hzk⟩ := hz
    refine ⟨k, ?_, hzk⟩
    change first ≤ k
    change depth + 1 ≤ k at hk
    omega

/-- A standard representative with specified nonzero digit belongs to its ray. -/
theorem ray_matches_representative (q depth digit : ℕ) (center : ℤ) :
    (Ray.mk q (depth + 1) center digit).Matches
      (center + (digit : ℤ) * (q : ℤ) ^ depth) := by
  refine ⟨depth + 1, le_rfl, ?_⟩
  simp [Ray.at, Congruence.Covers]

/-- A finite, explicit list containing a representative of each local ray
signature away from the finitely many exact centers. -/
def localRepresentatives (q depth : ℕ) (rays : List Ray) : List ℤ :=
  ((List.range (q ^ depth)).map fun n => (n : ℤ)) ++
    rays.flatMap fun r => ((List.range q).filter (1 ≤ ·)).map fun digit =>
      r.center + (digit : ℤ) * (q : ℤ) ^ depth

end Modulus40
