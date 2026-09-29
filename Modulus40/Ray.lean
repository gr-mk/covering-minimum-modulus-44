import Modulus40.Basic

/-!
# Arithmetic semantics of the paper's arrows

A ray is a family of congruence classes with moduli `q^k` for `k ≥ first`.
Its residues are `center + digit*q^(k-1)`. In the paper's notation for
`(q^m)↑` on the class `a (mod q^(m-1))`, `center = a-q^(m-1)`.

These definitions do not pretend that an infinite family is a finite covering
system. The truncation lemma below isolates exactly the residue class which
must be covered separately when a finite bound is chosen.
-/

namespace Modulus40

structure Ray where
  base : ℕ
  first : ℕ
  center : ℤ
  digit : ℕ
  deriving DecidableEq, Repr

/-- The congruence at one level of a ray. -/
def Ray.at (r : Ray) (k : ℕ) : Congruence :=
  ⟨r.base ^ k, r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)⟩

/-- Membership in at least one level of an infinite ray. -/
def Ray.Matches (r : Ray) (z : ℤ) : Prop :=
  ∃ k : ℕ, r.first ≤ k ∧ (r.at k).Covers z

/-- Finite initial segment, including level `bound`. -/
def Ray.truncate (r : Ray) (bound : ℕ) : List Congruence :=
  ((List.range (bound + 1)).filter (r.first ≤ ·)).map r.at

/-- The tail residue class left when a ray is truncated at `bound`. -/
def Ray.tail (r : Ray) (bound : ℕ) : Congruence :=
  ⟨r.base ^ bound, r.center⟩

/-- Every level beyond the truncation bound lies in the tail residue class. -/
theorem Ray.tail_covers_of_lt {r : Ray} {bound k : ℕ} {z : ℤ}
    (hk : bound < k) (hz : (r.at k).Covers z) :
    (r.tail bound).Covers z := by
  have hd : (r.base : ℤ) ^ bound ∣ (r.base : ℤ) ^ k :=
    pow_dvd_pow _ (Nat.le_of_lt hk)
  have hd' : (r.base : ℤ) ^ bound ∣ (r.base : ℤ) ^ (k - 1) :=
    pow_dvd_pow _ (by omega)
  have hz' : Int.ModEq ((r.base : ℤ) ^ k) z
      (r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)) := by
    simpa [Congruence.Covers, Ray.at, Int.ModEq] using hz
  have hcenter : Int.ModEq ((r.base : ℤ) ^ bound)
      (r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)) r.center := by
    apply Int.modEq_iff_dvd.mpr
    have heq : r.center - (r.center + (r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)) =
        -((r.digit : ℤ) * (r.base : ℤ) ^ (k - 1)) := by ring
    rw [heq]
    exact dvd_neg.mpr (dvd_mul_of_dvd_right hd' _)
  have h := (hz'.of_dvd hd).trans hcenter
  simpa [Congruence.Covers, Ray.tail, Int.ModEq] using h

/-- An integer matched by an infinite ray is covered by its finite truncation
unless it belongs to the explicitly identified tail. -/
theorem Ray.truncate_or_tail {r : Ray} {z : ℤ} (h : r.Matches z) (bound : ℕ) :
    (∃ c ∈ r.truncate bound, c.Covers z) ∨ (r.tail bound).Covers z := by
  obtain ⟨k, hlo, hz⟩ := h
  by_cases hk : k ≤ bound
  · left
    refine ⟨r.at k, ?_, hz⟩
    apply List.mem_map.mpr
    refine ⟨k, ?_, rfl⟩
    simp [List.mem_filter, List.mem_range, hlo, Nat.lt_succ_iff.mpr hk]
  · exact Or.inr (r.tail_covers_of_lt (by omega) hz)

/-- Away from the tail, an infinite ray match has a bounded witness. -/
theorem Ray.bounded_witness {r : Ray} {z : ℤ} {bound : ℕ}
    (htail : ¬ (r.tail bound).Covers z) (h : r.Matches z) :
    ∃ k, r.first ≤ k ∧ k ≤ bound ∧ (r.at k).Covers z := by
  obtain ⟨k, hlo, hz⟩ := h
  refine ⟨k, hlo, ?_, hz⟩
  by_contra hk
  exact htail (r.tail_covers_of_lt (by omega) hz)

end Modulus40
