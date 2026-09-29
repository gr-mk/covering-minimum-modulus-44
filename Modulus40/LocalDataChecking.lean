import Modulus40.LocalData

/-!
# Compact finite checks for local signature data

Distinct center blocks need only be checked once. Explicit indices select the
representative matching each compact sample, avoiding repeated existential
searches while proving the original `LocalData.Valid` predicate.
-/

namespace Modulus40

def compactCanonicalRepresentatives (q depth : ℕ) (rays : List Ray)
    (centers : List ℤ) : List ℤ :=
  (((List.range (q ^ depth)).map fun n : ℕ => (n : ℤ)).filter
    (fun z => rays.all (fun r => decide (¬ Int.ModEq (q ^ depth : ℕ) z r.center)))) ++
  centers.flatMap fun center => ((List.range q).filter (1 ≤ ·)).map fun digit : ℕ =>
    center + (digit : ℤ) * (q : ℤ) ^ depth

theorem canonicalRepresentatives_subset_compact {q depth : ℕ} {rays : List Ray}
    {centers : List ℤ} (hc : ∀ r ∈ rays, r.center ∈ centers) :
    ∀ w ∈ canonicalRepresentatives q depth rays,
      w ∈ compactCanonicalRepresentatives q depth rays centers := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact List.mem_append_left _ hw
  · obtain ⟨r, hr, hw⟩ := List.mem_flatMap.mp hw
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨r.center, hc r hr, hw⟩)

/-- The non-signature obligations in `LocalData.Valid`. -/
def LocalData.StructuralValid (data : LocalData) : Prop :=
  data.prime.Prime ∧
  (∀ r ∈ data.rays, r.base = data.prime) ∧
  (∀ r ∈ data.rays, 1 ≤ r.first ∧ r.first ≤ data.depth + 1) ∧
  (∀ r ∈ data.rays, 1 ≤ r.digit ∧ r.digit < data.prime) ∧
  (∀ r ∈ data.rays, ∀ s ∈ data.rays,
    Int.ModEq (data.prime ^ data.depth : ℕ) r.center s.center → r.center = s.center) ∧
  (∀ s ∈ data.coordinates, s.AccountedFor data.prime data.depth data.rays) ∧
  (∀ s ∈ data.coordinates, s.WellFormed data.prime) ∧
  (∀ r ∈ data.rays, Coordinate.ray r.first r.center r.digit ∈ data.coordinates)

instance instDecidableLocalDataStructuralValid (data : LocalData) :
    Decidable data.StructuralValid := by
  unfold LocalData.StructuralValid
  infer_instance

/-- Each sample has a supplied representative index with the same whole signature. -/
def LocalData.SignatureWitnessesValid (data : LocalData) (samples : List ℤ)
    (witnesses : List ℕ) : Prop :=
  if hlen : witnesses.length = samples.length then
    ∀ i : Fin samples.length,
      let representativeIndex := witnesses[i.val]'(by omega)
      if ha : representativeIndex < data.representatives.length then
        ∀ s ∈ data.coordinates, s.test data.prime samples[i.val] =
          s.test data.prime data.representatives[representativeIndex]
      else False
  else False

instance instDecidableLocalDataSignatureWitnessesValid (data : LocalData)
    (samples : List ℤ) (witnesses : List ℕ) :
    Decidable (data.SignatureWitnessesValid samples witnesses) := by
  unfold LocalData.SignatureWitnessesValid
  split_ifs <;> infer_instance

theorem LocalData.SignatureWitnessesValid.sound {data : LocalData}
    {samples : List ℤ} {witnesses : List ℕ}
    (h : data.SignatureWitnessesValid samples witnesses) :
    ∀ w ∈ samples, ∃ a ∈ data.representatives, ∀ s ∈ data.coordinates,
      s.test data.prime w = s.test data.prime a := by
  unfold LocalData.SignatureWitnessesValid at h
  split_ifs at h with hlen
  intro w hw
  obtain ⟨i, rfl⟩ := List.get_of_mem hw
  have hi := h i
  dsimp only at hi
  split_ifs at hi with ha
  exact ⟨_, List.getElem_mem ha, hi⟩

/-- Compact witness checks imply the full local validity statement used by the
all-integers realization theorem. -/
theorem LocalData.valid_of_compactWitnesses (data : LocalData) (centers : List ℤ)
    (witnesses : List ℕ) (hstruct : data.StructuralValid)
    (hcenters : ∀ r ∈ data.rays, r.center ∈ centers)
    (hw : data.SignatureWitnessesValid
      (compactCanonicalRepresentatives data.prime data.depth data.rays centers) witnesses) :
    data.Valid := by
  rcases hstruct with ⟨hp, hb, hf, hd, hsep, ha, hg, hsource⟩
  refine ⟨hp, hb, hf, hd, hsep, ha, hg, hsource, ?_⟩
  intro w hw'
  exact hw.sound w (canonicalRepresentatives_subset_compact hcenters w hw')

end Modulus40
