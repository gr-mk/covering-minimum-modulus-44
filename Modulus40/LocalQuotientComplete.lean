import Modulus40.LocalQuotient

/-!
# Soundness of the finite local quotient

All fixed residues outside central tail classes are represented at a common
finite depth. Each central tail has one representative for every nonzero digit.
The theorem proves that this is exhaustive, rather than assuming that finite
numerical sampling captures every integer.
-/

namespace Modulus40

/-- Ordinary representatives omit center residues; each such tail is represented
instead by its possible first nonzero digits. -/
def canonicalRepresentatives (q depth : ℕ) (rays : List Ray) : List ℤ :=
  (((List.range (q ^ depth)).map fun n : ℕ => (n : ℤ)).filter
    (fun z => rays.all (fun r => decide (¬ Int.ModEq (q ^ depth : ℕ) z r.center)))) ++
  rays.flatMap fun r => ((List.range q).filter (1 ≤ ·)).map fun digit : ℕ =>
    r.center + (digit : ℤ) * (q : ℤ) ^ depth

/-- The finite local representatives preserve every ray predicate in a given
finite collection, and every congruence modulo `q^depth`. -/
theorem exists_canonicalRepresentative {q depth : ℕ} (hq : q.Prime)
    (rays : List Ray)
    (hbase : ∀ r ∈ rays, r.base = q)
    (hfirst : ∀ r ∈ rays, 1 ≤ r.first ∧ r.first ≤ depth + 1)
    (hdigit : ∀ r ∈ rays, 1 ≤ r.digit ∧ r.digit < q)
    (hsep : ∀ r ∈ rays, ∀ s ∈ rays,
      Int.ModEq (q ^ depth : ℕ) r.center s.center → r.center = s.center)
    (z : ℤ) (hz : ∀ r ∈ rays, z ≠ r.center) :
    ∃ w ∈ canonicalRepresentatives q depth rays,
      Int.ModEq (q ^ depth : ℕ) z w ∧
      ∀ r ∈ rays, r.Matches z ↔ r.Matches w := by
  classical
  by_cases hnear : ∃ r ∈ rays, Int.ModEq (q ^ depth : ℕ) z r.center
  · obtain ⟨r₀, hr₀, hzr₀⟩ := hnear
    have hdiv : (q : ℤ) ^ depth ∣ z - r₀.center := by
      simpa using hzr₀.symm.dvd
    obtain ⟨digit, hd, hdq, hdeep⟩ := Ray.exists_digit_matches hq (hz r₀ hr₀) hdiv
    let w := r₀.center + (digit : ℤ) * (q : ℤ) ^ depth
    have hwdeep : (Ray.mk q (depth + 1) r₀.center digit).Matches w :=
      ray_matches_representative q depth digit r₀.center
    have hwc : Int.ModEq (q ^ depth : ℕ) w r₀.center := by
      simp [w, Int.ModEq, Int.add_emod]
    have hzw := hzr₀.trans hwc.symm
    refine ⟨w, ?_, hzw, ?_⟩
    · apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨r₀, hr₀, ?_⟩
      apply List.mem_map.mpr
      refine ⟨digit, ?_, rfl⟩
      simp [List.mem_filter, List.mem_range, hd, hdq]
    · intro r hr
      have hb := hbase r hr
      have hf := hfirst r hr
      have hdi := hdigit r hr
      by_cases hc : r.center = r₀.center
      · have hshape : r = Ray.mk q r.first r₀.center r.digit := by
          cases r
          simp_all
        rw [hshape]
        rw [ray_matches_iff_digit_of_deep_match hq hf.1 hf.2 hd hdq hdi.1 hdi.2 hdeep,
          ray_matches_iff_digit_of_deep_match hq hf.1 hf.2 hd hdq hdi.1 hdi.2 hwdeep]
      · have ht : ¬ (r.tail depth).Covers z := by
          intro ht
          have hzr : Int.ModEq (q ^ depth : ℕ) z r.center := by
            simpa [Ray.tail, Congruence.Covers, Int.ModEq, hb] using ht
          exact hc (hsep r hr r₀ hr₀ (hzr.symm.trans hzr₀))
        exact Ray.matches_iff_of_modEq_of_not_tail (by simpa [hb] using hzw) ht
  · have hfar : ∀ r ∈ rays, ¬ Int.ModEq (q ^ depth : ℕ) z r.center := by
      intro r hr hmod
      exact hnear ⟨r, hr, hmod⟩
    let modulus := q ^ depth
    have hm : (0 : ℤ) < modulus := by exact_mod_cast pow_pos hq.pos depth
    let w := z % (modulus : ℤ)
    have hw0 : 0 ≤ w := Int.emod_nonneg z (ne_of_gt hm)
    have hwlt : w < modulus := Int.emod_lt_of_pos z hm
    have hwcast : (w.toNat : ℤ) = w := Int.toNat_of_nonneg hw0
    have hwin : w.toNat < q ^ depth := by
      change w.toNat < modulus
      omega
    have hzw : Int.ModEq (q ^ depth : ℕ) z w := (Int.mod_modEq z modulus).symm
    refine ⟨w, ?_, hzw, ?_⟩
    · change w ∈ canonicalRepresentatives q depth rays
      simp only [canonicalRepresentatives, List.mem_append, List.mem_filter,
        List.mem_map, List.mem_range]
      left
      refine ⟨⟨w.toNat, hwin, hwcast⟩, ?_⟩
      simp only [List.all_eq_true, decide_eq_true_eq]
      intro r hr hwr
      exact hfar r hr (hzw.trans hwr)
    · intro r hr
      have hb := hbase r hr
      have ht : ¬ (r.tail depth).Covers z := by
        intro ht
        apply hfar r hr
        simpa [Ray.tail, Congruence.Covers, Int.ModEq, hb] using ht
      exact Ray.matches_iff_of_modEq_of_not_tail (by simpa [hb] using hzw) ht

end Modulus40
