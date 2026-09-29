import Modulus40.LocalDataChecking

/-!
# Chunked local-table validity (UC85 pilot family, new file)

`LocalData.valid_of_compactWitnesses` checks every compact sample in one `decide`; for large local tables
(depth 2 at p = 43, or p ≥ 197) that single kernel evaluation exceeds 32 GB.  `valid_of_chunks` needs only
`sigOK` at each sample index, which a generated module can discharge in many small `decide +kernel` blocks.
-/

namespace UC85
open Modulus40

/-- Sample `i` has a representative (its witness) with the same test on every coordinate. -/
def sigOK (data : LocalData) (samples : List ℤ) (witnesses : List ℕ) (i : ℕ) : Bool :=
  decide (witnesses.getD i 0 < data.representatives.length) &&
    data.coordinates.all fun s =>
      s.test data.prime (samples.getD i 0) ==
        s.test data.prime (data.representatives.getD (witnesses.getD i 0) 0)

theorem valid_of_chunks (data : LocalData) (centers samples : List ℤ) (witnesses : List ℕ)
    (hstruct : data.StructuralValid) (hcenters : ∀ r ∈ data.rays, r.center ∈ centers)
    (hsamples : compactCanonicalRepresentatives data.prime data.depth data.rays centers = samples)
    (hok : ∀ i < samples.length, sigOK data samples witnesses i = true) : data.Valid := by
  rcases hstruct with ⟨hp, hb, hf, hd, hsep, ha, hg, hsource⟩
  refine ⟨hp, hb, hf, hd, hsep, ha, hg, hsource, ?_⟩
  intro w hw
  have hw' := canonicalRepresentatives_subset_compact hcenters w hw
  rw [hsamples] at hw'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw'
  have h := hok i hi
  simp only [sigOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hw1, hall⟩ := h
  refine ⟨_, List.getElem_mem hw1, fun s hs => ?_⟩
  have := hall s hs
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hw1] at this

end UC85
