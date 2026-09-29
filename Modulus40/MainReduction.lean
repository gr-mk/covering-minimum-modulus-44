import Modulus40.IndexedCore
import Modulus40.CoordinateSemantics
import Modulus40.Realization

/-!
# Reduction of the paper to its finite symbolic certificate

A complete symbolic cover, up to the finitely many exact centers of its arrow
rays, gives a finite distinct covering system with minimum modulus exactly 40.
The proof chooses a common finite truncation depth and terminates all tails
with individually tagged powers of one fresh prime.
-/

namespace Modulus40

/-- Exact centers are the exceptional points omitted by an infinite arrow ray. -/
def Coordinate.IsRayCenter : Coordinate → ℤ → Prop
  | .fixed _ _, _ => False
  | .ray _ center _, z => z = center

/-- Fixed coordinates may also be capped harmlessly, making the tail indexing uniform. -/
def Coordinate.tailCenter : Coordinate → ℤ
  | .fixed _ residue => residue
  | .ray _ center _ => center

/-- Every coordinate is allocated a separate marker exponent. -/
def coordinateTails {d k : ℕ} (primes : Fin d → ℕ)
    (patterns : Fin k → PrimePattern d) : Fin (k * d) → ArrowTail := fun index =>
  let ij := finProdFinEquiv.symm index
  ⟨primes ij.2, (patterns ij.1 ij.2).tailCenter⟩

@[simp] theorem coordinateTails_pair {d k : ℕ} (primes : Fin d → ℕ)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (j : Fin d) :
    coordinateTails primes patterns (finProdFinEquiv (i, j)) =
      ⟨primes j, (patterns i j).tailCenter⟩ := by
  simp [coordinateTails]

/-- A coordinate tail is one of the globally capped holes. -/
theorem coordinateTail_mem {d k N : ℕ} (primes : Fin d → ℕ)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (j : Fin d) (z : ℤ)
    (ht : (patterns i j).InTail (primes j) N z) :
    ∃ index, Int.ModEq ((coordinateTails primes patterns index).base ^ N : ℕ)
      z (coordinateTails primes patterns index).center := by
  refine ⟨finProdFinEquiv (i, j), ?_⟩
  rw [coordinateTails_pair]
  cases hs : patterns i j with
  | fixed exponent residue => simp [Coordinate.InTail, hs] at ht
  | ray first center digit =>
    simpa [Coordinate.InTail, Coordinate.tailCenter, hs, Congruence.Covers,
      Int.ModEq] using ht

/-- Exact ray centers belong to every finite-depth tail around them. -/
theorem rayCenter_mem_tail {d k N : ℕ} (primes : Fin d → ℕ)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (j : Fin d) (z : ℤ)
    (hc : (patterns i j).IsRayCenter z) :
    ∃ index, Int.ModEq ((coordinateTails primes patterns index).base ^ N : ℕ)
      z (coordinateTails primes patterns index).center := by
  refine ⟨finProdFinEquiv (i, j), ?_⟩
  rw [coordinateTails_pair]
  cases hs : patterns i j with
  | fixed exponent residue => simp [Coordinate.IsRayCenter, hs] at hc
  | ray first center digit =>
    have hzc : z = center := by simpa [Coordinate.IsRayCenter, hs] using hc
    simp [Coordinate.tailCenter, hzc, Int.ModEq]

/-- The finite core covers everything except the explicitly capped tails. -/
theorem indexedCore_or_tail_of_symbolic {d k N : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d)
    (hlo : ∀ i j, (patterns i j).interval.lo ≤ N)
    (hcover : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z) (z : ℤ) :
    (∃ c ∈ indexedCore primes hprime hinj patterns N, c.Covers z) ∨
      ∃ index, Int.ModEq ((coordinateTails primes patterns index).base ^ N : ℕ)
        z (coordinateTails primes patterns index).center := by
  by_cases ht : ∃ index,
      Int.ModEq ((coordinateTails primes patterns index).base ^ N : ℕ)
        z (coordinateTails primes patterns index).center
  · exact Or.inr ht
  · left
    rcases hcover z with ⟨i, hi⟩ | ⟨i, j, hij⟩
    · have hnot : ¬ (patterns i).InTail primes N z := by
        rintro ⟨j, hj⟩
        exact ht (coordinateTail_mem primes patterns i j z hj)
      obtain ⟨e, he⟩ := PrimePattern.bounded_witness (hlo i) hi hnot
      apply indexedCore_covers primes hprime hinj patterns i (fun j => (e j).val)
      · exact fun j => (he j).1
      · intro j
        exact Nat.le_of_lt_succ (e j).isLt
      · exact fun j => (he j).2
    · exact False.elim (ht (rayCenter_mem_tail primes patterns i j z hij))

/-- At any sufficiently large common bound the symbolic certificate yields an
explicit finite completed covering system, with minimum exactly 40. -/
theorem complete_indexed_at_bound {d k N P : ℕ} (hP : P.Prime)
    (primes : Fin d → ℕ) (hprime : ∀ i, (primes i).Prime)
    (hinj : Function.Injective primes) (hfresh : ∀ i, ¬ P ∣ primes i)
    (patterns : Fin k → PrimePattern d)
    (hsep : ∀ i j, i ≠ j → (primePatternBoxes patterns i).Separated
      (primePatternBoxes patterns j))
    (hmin : ∀ i, 40 ≤ supportModulus primes
      (fun j => (patterns i j).interval.lo))
    (witness : Fin k) (exponents : ExponentVector d)
    (hw : (primePatternBoxes patterns witness).Contains exponents)
    (hwmod : supportModulus primes exponents = 40)
    (hlo : ∀ i j, (patterns i j).interval.lo ≤ N)
    (hwN : ∀ j, exponents j ≤ N) (hN : P ^ (k * d) - 1 + 6 ≤ N)
    (hcover : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z) :
    IsCoveringSystem (indexedCore primes hprime hinj patterns N ++
      allArrowCaps P N (coordinateTails primes patterns)) ∧
    HasSmallestModulus (indexedCore primes hprime hinj patterns N ++
      allArrowCaps P N (coordinateTails primes patterns)) 40 := by
  apply complete_by_arrowCaps hP
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

/-- The final finite-cover theorem requires only symbolic coverage, distinct
support boxes, checked minimum products, and one modulus-40 witness. -/
theorem minimumModulus40_of_symbolic {d k P : ℕ} (hP : P.Prime)
    (primes : Fin d → ℕ) (hprime : ∀ i, (primes i).Prime)
    (hinj : Function.Injective primes) (hfresh : ∀ i, ¬ P ∣ primes i)
    (patterns : Fin k → PrimePattern d)
    (hsep : ∀ i j, i ≠ j → (primePatternBoxes patterns i).Separated
      (primePatternBoxes patterns j))
    (hmin : ∀ i, 40 ≤ supportModulus primes
      (fun j => (patterns i j).interval.lo))
    (witness : Fin k) (exponents : ExponentVector d)
    (hw : (primePatternBoxes patterns witness).Contains exponents)
    (hwmod : supportModulus primes exponents = 40)
    (hcover : ∀ z : ℤ, (∃ i, (patterns i).Matches primes z) ∨
      ∃ i j, (patterns i j).IsRayCenter z) : MinimumModulus40 := by
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
  exact ⟨_, complete_indexed_at_bound hP primes hprime hinj hfresh patterns
    hsep hmin witness exponents hw hwmod hlo hwN hN hcover⟩

end Modulus40
