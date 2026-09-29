import Modulus40.MainReduction

/-!
# gr-mk's finite completion for any least modulus `n ≤ 64` and any fresh prime `P`

`Reduction42.lean` with n replaced by a parameter `n` (hypothesis `n ≤ 64`: every fresh-prime cap
has modulus at least `q ^ 6 ≥ 64`).  For the patched 43 use `n = 43` and a fresh `P ≥ 211`.
-/

namespace UC85
open Modulus40

/-- A finite distinct covering system with least modulus `n`. -/
def MinimumModulusN (n : ℕ) : Prop :=
  ∃ cs : List Congruence, IsCoveringSystem cs ∧ HasSmallestModulus cs n

theorem arrowCap_modulus_geN {n q m p : ℕ} (hn64 : n ≤ 64)
    (hq : 1 < q) (hp : 0 < p) (hm : p - 1 + 6 ≤ m)
    (center : ℤ) {c : Congruence} (hc : c ∈ arrowCap q m p center) :
    n ≤ c.modulus := by
  have hbound := arrowCap_modulus_lower_bound (by omega : 0 < q) hp hm center hc
  have hpower : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left (by omega) 6
  omega

theorem allArrowCaps_modulus_geN {n t P N : ℕ} (hn64 : n ≤ 64) (hP : P.Prime)
    (tails : Fin t → ArrowTail) (hbase : ∀ i, 1 < (tails i).base)
    (hN : P ^ t - 1 + 6 ≤ N) {c : Congruence}
    (hc : c ∈ allArrowCaps P N tails) :
    n ≤ c.modulus := by
  obtain ⟨i, hi⟩ := mem_allArrowCaps.mp hc
  exact arrowCap_modulus_geN hn64 (hbase i) (pow_pos hP.pos _)
    (indexedArrowCap_depth hP hN i) (tails i).center hi

theorem complete_by_arrowCapsN {n t P N : ℕ} (hn64 : n ≤ 64) (hn2 : 2 ≤ n) (hP : P.Prime)
    (core : List Congruence) (tails : Fin t → ArrowTail)
    (hbase : ∀ i, 1 < (tails i).base)
    (hfresh : ∀ i, ¬ P ∣ (tails i).base)
    (hN : P ^ t - 1 + 6 ≤ N)
    (hcoreDistinct : DistinctModuli core)
    (hcoreMin : HasSmallestModulus core n)
    (hcoreFresh : ∀ c ∈ core, ¬ P ∣ c.modulus)
    (hcover : ∀ z : ℤ, (∃ c ∈ core, c.Covers z) ∨
      ∃ i, Int.ModEq ((tails i).base ^ N : ℕ) z (tails i).center) :
    IsCoveringSystem (core ++ allArrowCaps P N tails) ∧
      HasSmallestModulus (core ++ allArrowCaps P N tails) n := by
  have hmin : ∀ c ∈ core ++ allArrowCaps P N tails, n ≤ c.modulus := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcoreMin.1 c hc
    · exact allArrowCaps_modulus_geN hn64 hP tails hbase hN hc
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

theorem complete_indexed_at_boundN {n d k N P : ℕ} (hn64 : n ≤ 64) (hn2 : 2 ≤ n) (hP : P.Prime)
    (primes : Fin d → ℕ) (hprime : ∀ i, (primes i).Prime)
    (hinj : Function.Injective primes) (hfresh : ∀ i, ¬ P ∣ primes i)
    (patterns : Fin k → PrimePattern d)
    (hsep : ∀ i j, i ≠ j → (primePatternBoxes patterns i).Separated
      (primePatternBoxes patterns j))
    (hmin : ∀ i, n ≤ supportModulus primes
      (fun j => (patterns i j).interval.lo))
    (witness : Fin k) (exponents : ExponentVector d)
    (hw : (primePatternBoxes patterns witness).Contains exponents)
    (hwmod : supportModulus primes exponents = n)
    (hlo : ∀ i j, (patterns i j).interval.lo ≤ N)
    (hwN : ∀ j, exponents j ≤ N) (hN : P ^ (k * d) - 1 + 6 ≤ N)
    (hcover : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z) :
    IsCoveringSystem (indexedCore primes hprime hinj patterns N ++
      allArrowCaps P N (coordinateTails primes patterns)) ∧
    HasSmallestModulus (indexedCore primes hprime hinj patterns N ++
      allArrowCaps P N (coordinateTails primes patterns)) n := by
  apply complete_by_arrowCapsN hn64 hn2 hP
    (indexedCore primes hprime hinj patterns N) (coordinateTails primes patterns)
  · intro index
    exact (hprime (finProdFinEquiv.symm index).2).one_lt
  · intro index
    exact hfresh (finProdFinEquiv.symm index).2
  · exact hN
  · exact indexedCore_distinct primes hprime hinj patterns hsep
  · constructor
    · intro c hc
      exact indexedCore_modulus_lower_bound primes hprime hinj patterns hmin hc
    · exact indexedCore_attains primes hprime hinj patterns witness exponents hw hwN hwmod
  · intro c hc
    exact indexedCore_not_dvd hP primes hprime hinj hfresh patterns hc
  · exact indexedCore_or_tail_of_symbolic primes hprime hinj patterns hlo hcover

/-- Symbolic coverage (ray centres excepted), separated support boxes, least product `n` and
one modulus-`n` witness give a finite distinct covering system with least modulus `n`. -/
theorem minimumModulusN_of_symbolic {n d k P : ℕ} (hn64 : n ≤ 64) (hn2 : 2 ≤ n) (hP : P.Prime)
    (primes : Fin d → ℕ) (hprime : ∀ i, (primes i).Prime)
    (hinj : Function.Injective primes) (hfresh : ∀ i, ¬ P ∣ primes i)
    (patterns : Fin k → PrimePattern d)
    (hsep : ∀ i j, i ≠ j → (primePatternBoxes patterns i).Separated
      (primePatternBoxes patterns j))
    (hmin : ∀ i, n ≤ supportModulus primes
      (fun j => (patterns i j).interval.lo))
    (witness : Fin k) (exponents : ExponentVector d)
    (hw : (primePatternBoxes patterns witness).Contains exponents)
    (hwmod : supportModulus primes exponents = n)
    (hcover : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z) : MinimumModulusN n := by
  let N := P ^ (k * d) + 6 + (∑ i, ∑ j, (patterns i j).interval.lo) + ∑ j, exponents j
  have hlo : ∀ i j, (patterns i j).interval.lo ≤ N := by
    intro i j
    have h1 : (patterns i j).interval.lo ≤ ∑ j, (patterns i j).interval.lo :=
      Finset.single_le_sum (f := fun j : Fin d => (patterns i j).interval.lo)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j, (patterns i j).interval.lo) ≤ ∑ i, ∑ j, (patterns i j).interval.lo :=
      Finset.single_le_sum (f := fun i : Fin k => ∑ j, (patterns i j).interval.lo)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [N]
    omega
  have hwN : ∀ j, exponents j ≤ N := by
    intro j
    have h : exponents j ≤ ∑ j, exponents j :=
      Finset.single_le_sum (f := exponents) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    dsimp [N]
    omega
  have hN : P ^ (k * d) - 1 + 6 ≤ N := by dsimp [N]; omega
  exact ⟨_, complete_indexed_at_boundN hn64 hn2 hP primes hprime hinj hfresh patterns
    hsep hmin witness exponents hw hwmod hlo hwN hN hcover⟩

end UC85
