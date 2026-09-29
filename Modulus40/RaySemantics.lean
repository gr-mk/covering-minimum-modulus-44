import Modulus40.Ray
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Nonzero digits of prime-power rays

Every noncentral integer in a residue class has a first nonzero base-prime
digit. This gives the precise finite choice of rays covering that class away
from its center.
-/

namespace Modulus40

/-- A nonzero integer has a unique maximal power of a prime dividing it. -/
theorem exists_prime_power_factor {q : ℕ} (hq : q.Prime) {x : ℤ} (hx : x ≠ 0) :
    ∃ n : ℕ, ∃ u : ℤ, x = (q : ℤ) ^ n * u ∧ ¬ (q : ℤ) ∣ u := by
  letI : Fact q.Prime := ⟨hq⟩
  let n := padicValInt q x
  obtain ⟨u, hu⟩ := padicValInt_dvd (p := q) x
  refine ⟨n, u, hu, ?_⟩
  rintro ⟨v, hv⟩
  have hd : (q : ℤ) ^ (n + 1) ∣ x := by
    refine ⟨v, ?_⟩
    rw [hu, hv, pow_succ]
    ring
  have hle := (padicValInt_dvd_iff (p := q) (n + 1) x).mp hd
  rcases hle with hzero | hle
  · exact hx hzero
  · simp [n] at hle

/-- Removing a sufficiently large prime power from a nonzero integer leaves a
nonzero digit modulo the prime. -/
theorem exists_prime_digit_factor {q m : ℕ} (hq : q.Prime) {x : ℤ}
    (hx : x ≠ 0) (hm : (q : ℤ) ^ m ∣ x) :
    ∃ n : ℕ, ∃ u : ℤ, m ≤ n ∧ x = (q : ℤ) ^ n * u ∧ ¬ (q : ℤ) ∣ u := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, u, hu, hunit⟩ := exists_prime_power_factor hq hx
  have hmn : m ≤ n := by
    by_contra hnot
    have hnm : n + 1 ≤ m := by omega
    have hd : (q : ℤ) ^ (n + 1) ∣ x := (pow_dvd_pow _ hnm).trans hm
    rw [hu, pow_succ] at hd
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
    exact hunit ((mul_dvd_mul_iff_left (pow_ne_zero n hq0)).mp hd)
  exact ⟨n, u, hmn, hu, hunit⟩

/-- The prime-power class of a center is covered, away from that center, by
its `q - 1` rays having nonzero digits. -/
theorem Ray.exists_digit_matches {q m : ℕ} (hq : q.Prime) {center z : ℤ}
    (hz : z ≠ center) (hm : (q : ℤ) ^ m ∣ z - center) :
    ∃ digit : ℕ, 1 ≤ digit ∧ digit < q ∧
      (Ray.mk q (m + 1) center digit).Matches z := by
  obtain ⟨n, u, hmn, hu, hunit⟩ := exists_prime_digit_factor hq (sub_ne_zero.mpr hz) hm
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq.pos
  have hnonneg : 0 ≤ u % (q : ℤ) := Int.emod_nonneg _ (ne_of_gt hqpos)
  have hlt : u % (q : ℤ) < q := Int.emod_lt_of_pos _ hqpos
  have hnonzero : u % (q : ℤ) ≠ 0 := by
    exact fun h => hunit (Int.dvd_of_emod_eq_zero h)
  let digit := (u % (q : ℤ)).toNat
  have hcast : (digit : ℤ) = u % (q : ℤ) := Int.toNat_of_nonneg hnonneg
  refine ⟨digit, by omega, by omega, n + 1, by change m + 1 ≤ n + 1; omega, ?_⟩
  have hmod : Int.ModEq (q : ℤ) u (digit : ℤ) := by
    rw [hcast]
    exact (Int.mod_modEq u q).symm
  have hmul := hmod.mul_right' (c := (q : ℤ) ^ n)
  have hz' : z = center + u * (q : ℤ) ^ n := by linear_combination hu
  simpa only [Congruence.Covers, Ray.at, Nat.add_sub_cancel, Nat.cast_pow, Nat.cast_mul,
    Int.ModEq, pow_succ', hz'] using hmul.add_left center

/-- At level `k`, a ray with a nonzero digit never matches its center modulo
`q^k`. In particular it contributes precisely at valuation `k - 1`. -/
theorem Ray.not_next_power_dvd_of_at_covers {r : Ray} (hq : r.base.Prime)
    (hdigit : 1 ≤ r.digit) (hdigit_lt : r.digit < r.base)
    {k : ℕ} (hk : 1 ≤ k) {z : ℤ} (hz : (r.at k).Covers z) :
    ¬ (r.base : ℤ) ^ k ∣ z - r.center := by
  have hmod : Int.ModEq ((r.base : ℤ) ^ k) z
      (r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)) := by
    simpa [Ray.at, Congruence.Covers, Int.ModEq] using hz
  intro hd
  have hsum := dvd_add hmod.dvd hd
  have heq : r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1) - z +
      (z - r.center) = (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1) := by ring
  rw [heq] at hsum
  have hpow : (r.base : ℤ) ^ k = (r.base : ℤ) * (r.base : ℤ) ^ (k - 1) := by
    calc
      (r.base : ℤ) ^ k = (r.base : ℤ) ^ ((k - 1) + 1) := by congr 1; omega
      _ = _ := pow_succ' _ _
  rw [hpow] at hsum
  have hq0 : (r.base : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hdiv := (mul_dvd_mul_iff_right (pow_ne_zero (k - 1) hq0)).mp hsum
  have hdiv' := Int.natCast_dvd_natCast.mp hdiv
  exact Nat.not_dvd_of_pos_of_lt (by omega) hdigit_lt hdiv'

/-- A valid ray matches a given noncentral integer at just one possible level,
one more than the prime-adic valuation of its displacement from the center. -/
theorem Ray.level_eq_padicVal_add_one {r : Ray} (hq : r.base.Prime)
    (hdigit : 1 ≤ r.digit) (hdigit_lt : r.digit < r.base)
    {k : ℕ} (hk : 1 ≤ k) {z : ℤ} (hz : (r.at k).Covers z) :
    k = padicValInt r.base (z - r.center) + 1 := by
  letI : Fact r.base.Prime := ⟨hq⟩
  have hn := r.not_next_power_dvd_of_at_covers hq hdigit hdigit_lt hk hz
  have hprev := r.tail_covers_of_lt (show k - 1 < k by omega) hz
  have hdivprev : (r.base : ℤ) ^ (k - 1) ∣ z - r.center := by
    have hmod : Int.ModEq ((r.base : ℤ) ^ (k - 1)) z r.center := by
      simpa [Ray.tail, Congruence.Covers, Int.ModEq] using hprev
    exact hmod.symm.dvd
  have hle := (padicValInt_dvd_iff (p := r.base) (k - 1) (z - r.center)).mp hdivprev
  have hnle : ¬ (z - r.center = 0 ∨ k ≤ padicValInt r.base (z - r.center)) := by
    rwa [← padicValInt_dvd_iff]
  omega

/-- Infinite existential ray membership reduces to its unique valuation level. -/
theorem Ray.matches_iff_at_padicVal {r : Ray} (hq : r.base.Prime)
    (hfirst : 1 ≤ r.first) (hdigit : 1 ≤ r.digit) (hdigit_lt : r.digit < r.base)
    (z : ℤ) :
    r.Matches z ↔
      r.first ≤ padicValInt r.base (z - r.center) + 1 ∧
      (r.at (padicValInt r.base (z - r.center) + 1)).Covers z := by
  constructor
  · rintro ⟨k, hk, hz⟩
    have heq := r.level_eq_padicVal_add_one hq hdigit hdigit_lt (by omega) hz
    exact heq ▸ ⟨hk, hz⟩
  · intro h
    exact ⟨_, h⟩

/-- Valid rays exclude their centers. This exceptional point must be handled
separately when rays are used in a finite covering construction. -/
theorem Ray.not_matches_center {r : Ray} (hq : r.base.Prime)
    (hfirst : 1 ≤ r.first) (hdigit : 1 ≤ r.digit) (hdigit_lt : r.digit < r.base) :
    ¬ r.Matches r.center := by
  rintro ⟨k, hk, hz⟩
  exact r.not_next_power_dvd_of_at_covers hq hdigit hdigit_lt (by omega) hz
    (by simp)

/-- Membership at any level at most `bound` depends only on the residue
modulo `base^bound`. -/
theorem Ray.at_covers_iff_of_modEq {r : Ray} {bound k : ℕ} (hk : k ≤ bound)
    {z w : ℤ} (hzw : Int.ModEq ((r.base : ℤ) ^ bound) z w) :
    (r.at k).Covers z ↔ (r.at k).Covers w := by
  have hsmall := hzw.of_dvd (pow_dvd_pow (r.base : ℤ) hk)
  change Int.ModEq ((r.base ^ k : ℕ) : ℤ) z (r.at k).residue ↔
    Int.ModEq ((r.base ^ k : ℕ) : ℤ) w (r.at k).residue
  rw [Nat.cast_pow]
  exact ⟨fun h => hsmall.symm.trans h, fun h => hsmall.trans h⟩

/-- Away from the central residue class, the truth of an entire ray is
constant on a residue class modulo `base^bound`. -/
theorem Ray.matches_iff_of_modEq_of_not_tail {r : Ray} {bound : ℕ}
    {z w : ℤ} (hzw : Int.ModEq ((r.base : ℤ) ^ bound) z w)
    (htail : ¬ (r.tail bound).Covers z) :
    r.Matches z ↔ r.Matches w := by
  have htail' : ¬ (r.tail bound).Covers w := by
    intro hw
    apply htail
    have hw' : Int.ModEq ((r.base : ℤ) ^ bound) w r.center := by
      simpa [Ray.tail, Congruence.Covers, Int.ModEq] using hw
    simpa [Ray.tail, Congruence.Covers, Int.ModEq] using hzw.trans hw'
  constructor
  · intro hz
    obtain ⟨k, hfirst, hk, hzk⟩ := r.bounded_witness htail hz
    exact ⟨k, hfirst, (r.at_covers_iff_of_modEq hk hzw).mp hzk⟩
  · intro hw
    obtain ⟨k, hfirst, hk, hwk⟩ := r.bounded_witness htail' hw
    exact ⟨k, hfirst, (r.at_covers_iff_of_modEq hk hzw).mpr hwk⟩

end Modulus40
