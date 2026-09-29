import Modulus40.Arrow

/-!
# Simultaneous finite termination of all arrow tails

The tails can be capped globally. Their auxiliary moduli are different powers
of one fresh prime, so no modulus is repeated across caps or with the core.
-/

namespace Modulus40

/-- An exceptional prime-power ray is centered at a fixed integer. -/
structure ArrowTail where
  base : ℕ
  center : ℤ
  deriving DecidableEq, Repr

/-- Tail `i` receives marker exponent `i + 1`. -/
def indexedArrowCap {t : ℕ} (P N : ℕ) (tails : Fin t → ArrowTail) (i : Fin t) :
    List Congruence :=
  arrowCap (tails i).base N (P ^ (i.val + 1)) (tails i).center

/-- A finite cap for every exceptional tail. -/
def allArrowCaps {t : ℕ} (P N : ℕ) (tails : Fin t → ArrowTail) : List Congruence :=
  (List.finRange t).flatMap (indexedArrowCap P N tails)

@[simp] theorem mem_allArrowCaps {t P N : ℕ} {tails : Fin t → ArrowTail}
    {c : Congruence} :
    c ∈ allArrowCaps P N tails ↔ ∃ i, c ∈ indexedArrowCap P N tails i := by
  simp [allArrowCaps, List.mem_flatMap]

/-- A shared depth suffices for every marker exponent in a finite family. -/
theorem indexedArrowCap_depth {t P N : ℕ} (hP : P.Prime)
    (hN : P ^ t - 1 + 6 ≤ N) (i : Fin t) :
    P ^ (i.val + 1) - 1 + 6 ≤ N := by
  have hp : P ^ (i.val + 1) ≤ P ^ t :=
    Nat.pow_le_pow_right hP.pos (by have := i.isLt; omega)
  omega

/-- The full cap family covers every tail at the common truncation depth. -/
theorem allArrowCaps_covers {t P N : ℕ} (hP : P.Prime)
    (tails : Fin t → ArrowTail) (i : Fin t) (z : ℤ)
    (hz : Int.ModEq ((tails i).base ^ N : ℕ) z (tails i).center) :
    ∃ c ∈ allArrowCaps P N tails, c.Covers z := by
  obtain ⟨c, hc, hz⟩ := arrowCap_covers (pow_pos hP.pos _) (tails i).center z hz
  exact ⟨c, mem_allArrowCaps.mpr ⟨i, hc⟩, hz⟩

/-- All ordinary and auxiliary factors in different caps remain distinguishable. -/
theorem allArrowCaps_distinct {t P N : ℕ} (hP : P.Prime)
    (tails : Fin t → ArrowTail)
    (hbase : ∀ i, 1 < (tails i).base)
    (hfresh : ∀ i, ¬ P ∣ (tails i).base)
    (hN : P ^ t - 1 + 6 ≤ N) :
    DistinctModuli (allArrowCaps P N tails) := by
  unfold DistinctModuli allArrowCaps
  rw [List.map_flatMap, List.nodup_flatMap]
  constructor
  · intro i _
    exact arrowCap_distinct (hbase i) (pow_pos hP.pos _)
      (by have := indexedArrowCap_depth hP hN i; omega) (tails i).center
  · apply (List.nodup_finRange t).pairwise_of_forall_ne
    intro i _ j _ hij
    apply List.disjoint_left.mpr
    intro m hmi hmj
    obtain ⟨c, hc, hcm⟩ := List.mem_map.mp hmi
    obtain ⟨d, hd, hdm⟩ := List.mem_map.mp hmj
    have htag : i.val + 1 ≠ j.val + 1 := by
      intro h
      apply hij
      apply Fin.ext
      omega
    exact arrowCap_moduli_ne hP (hfresh i) (hfresh j) htag
      (tails i).center (tails j).center hc hd (hcm.trans hdm.symm)

/-- Each added class meets the required lower bound. -/
theorem allArrowCaps_modulus_ge40 {t P N : ℕ} (hP : P.Prime)
    (tails : Fin t → ArrowTail) (hbase : ∀ i, 1 < (tails i).base)
    (hN : P ^ t - 1 + 6 ≤ N) {c : Congruence}
    (hc : c ∈ allArrowCaps P N tails) :
    40 ≤ c.modulus := by
  obtain ⟨i, hi⟩ := mem_allArrowCaps.mp hc
  exact arrowCap_modulus_ge40 (hbase i) (pow_pos hP.pos _)
    (indexedArrowCap_depth hP hN i) (tails i).center hi

/-- None of the added moduli can equal a modulus free of the marker prime. -/
theorem allArrowCaps_modulus_ne_core {t P N core : ℕ} (hP : P.Prime)
    (tails : Fin t → ArrowTail) (hfresh : ∀ i, ¬ P ∣ (tails i).base)
    (hcore : ¬ P ∣ core) {c : Congruence} (hc : c ∈ allArrowCaps P N tails) :
    c.modulus ≠ core := by
  obtain ⟨i, hi⟩ := mem_allArrowCaps.mp hc
  exact arrowCap_modulus_ne_core hP (hfresh i) (by omega) hcore (tails i).center hi

/-- A distinct finite core covering everything outside its tail holes can always
be completed to a finite distinct covering system, preserving modulus 40. -/
theorem complete_by_arrowCaps {t P N : ℕ} (hP : P.Prime)
    (core : List Congruence) (tails : Fin t → ArrowTail)
    (hbase : ∀ i, 1 < (tails i).base)
    (hfresh : ∀ i, ¬ P ∣ (tails i).base)
    (hN : P ^ t - 1 + 6 ≤ N)
    (hcoreDistinct : DistinctModuli core)
    (hcoreMin : HasSmallestModulus core 40)
    (hcoreFresh : ∀ c ∈ core, ¬ P ∣ c.modulus)
    (hcover : ∀ z : ℤ, (∃ c ∈ core, c.Covers z) ∨
      ∃ i, Int.ModEq ((tails i).base ^ N : ℕ) z (tails i).center) :
    IsCoveringSystem (core ++ allArrowCaps P N tails) ∧
      HasSmallestModulus (core ++ allArrowCaps P N tails) 40 := by
  have hmin : ∀ c ∈ core ++ allArrowCaps P N tails, 40 ≤ c.modulus := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcoreMin.1 c hc
    · exact allArrowCaps_modulus_ge40 hP tails hbase hN hc
  refine ⟨⟨?_, ?_, ?_⟩, hmin, ?_⟩
  · intro z
    rcases hcover z with ⟨c, hc, hz⟩ | ⟨i, hz⟩
    · exact ⟨c, List.mem_append_left _ hc, hz⟩
    · obtain ⟨c, hc, hz⟩ := allArrowCaps_covers hP tails i z hz
      exact ⟨c, List.mem_append_right _ hc, hz⟩
  · unfold DistinctModuli
    rw [List.map_append, List.nodup_append]
    refine ⟨hcoreDistinct, allArrowCaps_distinct hP tails hbase hfresh hN, ?_⟩
    intro m hm n hn
    obtain ⟨c, hc, hcm⟩ := List.mem_map.mp hm
    obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hn
    have hne := allArrowCaps_modulus_ne_core hP tails hfresh (hcoreFresh c hc) hd
    rw [hcm, hdn] at hne
    exact hne.symm
  · intro c hc
    have := hmin c hc
    omega
  · obtain ⟨c, hc, hcm⟩ := hcoreMin.2
    exact ⟨c, List.mem_append_left _ hc, hcm⟩

end Modulus40
