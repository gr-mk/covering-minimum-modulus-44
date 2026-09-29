import Modulus40.LocalCertificate
import Mathlib.Data.Nat.Bitwise

/-!
# Local data consumed by the rectangle certificate

All fields are finite data. `Valid` spells out every arithmetic and finite
signature check, and its soundness theorem ranges over all integers.
-/

namespace Modulus40

structure LocalData where
  prime : ℕ
  depth : ℕ
  rays : List Ray
  coordinates : List Coordinate
  representatives : List ℤ
  deriving DecidableEq, Repr

/-- No coverage conclusion is a field of the certificate. -/
def LocalData.Valid (data : LocalData) : Prop :=
  data.prime.Prime ∧
  (∀ r ∈ data.rays, r.base = data.prime) ∧
  (∀ r ∈ data.rays, 1 ≤ r.first ∧ r.first ≤ data.depth + 1) ∧
  (∀ r ∈ data.rays, 1 ≤ r.digit ∧ r.digit < data.prime) ∧
  (∀ r ∈ data.rays, ∀ s ∈ data.rays,
    Int.ModEq (data.prime ^ data.depth : ℕ) r.center s.center → r.center = s.center) ∧
  (∀ s ∈ data.coordinates, s.AccountedFor data.prime data.depth data.rays) ∧
  (∀ s ∈ data.coordinates, s.WellFormed data.prime) ∧
  (∀ r ∈ data.rays, Coordinate.ray r.first r.center r.digit ∈ data.coordinates) ∧
  (∀ w ∈ canonicalRepresentatives data.prime data.depth data.rays,
    ∃ a ∈ data.representatives, ∀ s ∈ data.coordinates,
      s.test data.prime w = s.test data.prime a)

instance instDecidableLocalDataValid (data : LocalData) : Decidable data.Valid := by
  unfold LocalData.Valid
  infer_instance

/-- A validated local data table represents every noncentral integer. -/
theorem LocalData.realizes (data : LocalData) (hv : data.Valid) (z : ℤ)
    (hz : ∀ s ∈ data.coordinates, ¬ s.IsRayCenter z) :
    ∃ a ∈ data.representatives, ∀ s ∈ data.coordinates,
      s.Matches data.prime z ↔ s.Matches data.prime a := by
  rcases hv with ⟨hp, hb, hf, hd, hsep, ha, hg, hsource, hfinite⟩
  apply local_signature_realization hp data.rays data.coordinates data.representatives
    hb hf hd hsep ha hg hfinite z
  intro r hr heq
  exact hz (.ray r.first r.center r.digit) (hsource r hr) heq

/-- Encode a finite Boolean list as an ordinary natural-number bit mask. -/
def boolMask : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (boolMask bs)

theorem boolMask_testBit (bs : List Bool) (i : Fin bs.length) :
    (boolMask bs).testBit i.val = bs.get i := by
  induction bs with
  | nil => exact Fin.elim0 i
  | cons b bs ih =>
    cases i using Fin.cases with
    | zero => simp [boolMask, Nat.testBit_bit_zero]
    | succ i => simpa [boolMask, Nat.testBit_bit_succ] using ih i

def Coordinate.mask (s : Coordinate) (p : ℕ) (representatives : List ℤ) : ℕ :=
  boolMask (representatives.map (s.test p))

/-- Each bit in an arithmetic coordinate mask has its proved test meaning. -/
theorem Coordinate.mask_testBit (s : Coordinate) (p : ℕ) (representatives : List ℤ)
    (i : Fin representatives.length) :
    (s.mask p representatives).testBit i.val = s.test p (representatives.get i) := by
  simpa [Coordinate.mask] using
    boolMask_testBit (representatives.map (s.test p)) ⟨i.val, by simpa using i.isLt⟩

end Modulus40
