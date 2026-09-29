import Modulus40.Coordinate
import Modulus40.CRT

/-!
# A finite core indexed by prime exponent vectors

Enumerating bounded exponent vectors with a `Finset` guarantees that no vector
is repeated. The support-box theorem then guarantees distinct moduli. Each
vector's residue is realized by the Chinese remainder theorem.
-/

namespace Modulus40

abbrev BoundedExponentVector (d N : ℕ) := Fin d → Fin (N + 1)

def BoundedExponentVector.toExponents {d N : ℕ} (e : BoundedExponentVector d N) :
    ExponentVector d := fun i => (e i).val

/-- All bounded supported entries, without duplicates. -/
noncomputable def boundedEntries {d k : ℕ} (boxes : Fin k → SupportBox d) (N : ℕ) :
    List (Fin k × BoundedExponentVector d N) :=
  (Finset.univ.filter fun entry => (boxes entry.1).Contains entry.2.toExponents).toList

@[simp] theorem mem_boundedEntries {d k N : ℕ} {boxes : Fin k → SupportBox d}
    {entry : Fin k × BoundedExponentVector d N} :
    entry ∈ boundedEntries boxes N ↔ (boxes entry.1).Contains entry.2.toExponents := by
  simp [boundedEntries]

theorem boundedEntries_nodup {d k : ℕ} (boxes : Fin k → SupportBox d) (N : ℕ) :
    (boundedEntries boxes N).Nodup := Finset.nodup_toList _

/-- Pairwise distinct prime coordinates always produce relatively prime factors. -/
theorem coordinateFactors_pairwise {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (pattern : PrimePattern d) (e : ExponentVector d) :
    (List.ofFn fun i => (pattern i).at (primes i) (e i)).Pairwise
      (fun c d => Nat.Coprime c.modulus d.modulus) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  change Nat.Coprime (primes i ^ e i) (primes j ^ e j)
  apply Nat.Coprime.pow
  apply (Nat.coprime_primes (hprime i) (hprime j)).mpr
  exact fun h => (ne_of_lt hij) (hinj h)

theorem coordinateFactors_positive {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (pattern : PrimePattern d) (e : ExponentVector d) :
    ∀ c ∈ (List.ofFn fun i => (pattern i).at (primes i) (e i)), 0 < c.modulus := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact pow_pos (hprime i).pos _

/-- A single exponent vector determines one congruence class by CRT. -/
def indexedCongruence {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (pattern : PrimePattern d) (e : ExponentVector d) : Congruence :=
  combineCongruences (List.ofFn fun i => (pattern i).at (primes i) (e i))
    (coordinateFactors_pairwise primes hprime hinj pattern e)

@[simp] theorem indexedCongruence_modulus {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (pattern : PrimePattern d) (e : ExponentVector d) :
    (indexedCongruence primes hprime hinj pattern e).modulus = supportModulus primes e := by
  simp [indexedCongruence, List.map_ofFn, List.prod_ofFn, supportModulus]

theorem indexedCongruence_covers_iff {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (pattern : PrimePattern d) (e : ExponentVector d) (z : ℤ) :
    (indexedCongruence primes hprime hinj pattern e).Covers z ↔
      ∀ i, ((pattern i).at (primes i) (e i)).Covers z := by
  unfold indexedCongruence
  rw [combineCongruences_covers_iff _ _
    (coordinateFactors_positive primes hprime pattern e)]
  simp [List.mem_ofFn]

/-- The ordinary finite core at the chosen exponent bound. -/
noncomputable def indexedCore {d k : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d) (N : ℕ) : List Congruence :=
  (boundedEntries (primePatternBoxes patterns) N).map fun entry =>
    indexedCongruence primes hprime hinj (patterns entry.1) entry.2.toExponents

/-- Membership exposes the corresponding bounded supported exponent vector. -/
theorem indexedCore_origin {d k N : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d) {c : Congruence}
    (hc : c ∈ indexedCore primes hprime hinj patterns N) :
    ∃ (i : Fin k) (e : ExponentVector d), (primePatternBoxes patterns i).Contains e ∧
      (∀ j, e j ≤ N) ∧ c = indexedCongruence primes hprime hinj (patterns i) e := by
  obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hc
  refine ⟨entry.1, entry.2.toExponents, mem_boundedEntries.mp he, ?_, rfl⟩
  intro j
  have := (entry.2 j).isLt
  exact Nat.le_of_lt_succ this

/-- Every bounded supported vector occurs in the finite core. -/
theorem indexedCongruence_mem_core {d k N : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (e : ExponentVector d)
    (he : (primePatternBoxes patterns i).Contains e) (hN : ∀ j, e j ≤ N) :
    indexedCongruence primes hprime hinj (patterns i) e ∈
      indexedCore primes hprime hinj patterns N := by
  let eb : BoundedExponentVector d N := fun j => ⟨e j, Nat.lt_succ_of_le (hN j)⟩
  apply List.mem_map.mpr
  refine ⟨(i, eb), mem_boundedEntries.mpr he, rfl⟩

/-- Bounded coordinate witnesses give an actual member of the finite core. -/
theorem indexedCore_covers {d k N : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (e : ExponentVector d)
    (he : (primePatternBoxes patterns i).Contains e) (hN : ∀ j, e j ≤ N)
    (z : ℤ) (hz : ∀ j, ((patterns i j).at (primes j) (e j)).Covers z) :
    ∃ c ∈ indexedCore primes hprime hinj patterns N, c.Covers z := by
  exact ⟨indexedCongruence primes hprime hinj (patterns i) e,
    indexedCongruence_mem_core primes hprime hinj patterns i e he hN,
    (indexedCongruence_covers_iff primes hprime hinj (patterns i) e z).mpr hz⟩

/-- Distinctness of boxes and the finite vector enumeration implies distinct
moduli for all ordinary core classes. -/
theorem indexedCore_distinct {d k N : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d)
    (hsep : ∀ i j, i ≠ j → (primePatternBoxes patterns i).Separated
      (primePatternBoxes patterns j)) :
    DistinctModuli (indexedCore primes hprime hinj patterns N) := by
  unfold DistinctModuli indexedCore
  rw [List.map_map]
  apply List.Nodup.map_on _ (boundedEntries_nodup _ N)
  intro x hx y hy h
  simp only [Function.comp_apply, indexedCongruence_modulus] at h
  obtain ⟨hindex, hexp⟩ := (supported_modulus_eq_iff primes hprime hinj
    (primePatternBoxes patterns) hsep (mem_boundedEntries.mp hx)
    (mem_boundedEntries.mp hy)).mp h
  apply Prod.ext hindex
  funext j
  exact Fin.ext (congrFun hexp j)

/-- Checked lower-endpoint products establish the minimum bound uniformly in N. -/
theorem indexedCore_modulus_lower_bound {d k N minimum : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d)
    (hmin : ∀ i, minimum ≤ supportModulus primes
      (fun j => (primePatternBoxes patterns i j).lo))
    {c : Congruence} (hc : c ∈ indexedCore primes hprime hinj patterns N) :
    minimum ≤ c.modulus := by
  obtain ⟨i, e, he, _, rfl⟩ := indexedCore_origin primes hprime hinj patterns hc
  rw [indexedCongruence_modulus]
  exact (hmin i).trans
    (SupportBox.modulus_lower_bound primes (fun j => (hprime j).pos) _ he)

/-- A prime absent from the base vector is absent from every core modulus. -/
theorem indexedCore_not_dvd {d k N P : ℕ} (hP : P.Prime) (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (hfresh : ∀ i, ¬ P ∣ primes i) (patterns : Fin k → PrimePattern d)
    {c : Congruence} (hc : c ∈ indexedCore primes hprime hinj patterns N) :
    ¬ P ∣ c.modulus := by
  obtain ⟨i, e, _, _, rfl⟩ := indexedCore_origin primes hprime hinj patterns hc
  rw [indexedCongruence_modulus]
  exact supportModulus_not_dvd hP primes hfresh e

/-- One bounded supported vector attains a specified modulus in the core. -/
theorem indexedCore_attains {d k N modulus : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (patterns : Fin k → PrimePattern d) (i : Fin k) (e : ExponentVector d)
    (he : (primePatternBoxes patterns i).Contains e) (hN : ∀ j, e j ≤ N)
    (hmod : supportModulus primes e = modulus) :
    ∃ c ∈ indexedCore primes hprime hinj patterns N, c.modulus = modulus := by
  refine ⟨indexedCongruence primes hprime hinj (patterns i) e,
    indexedCongruence_mem_core primes hprime hinj patterns i e he hN, ?_⟩
  simpa using hmod

end Modulus40
