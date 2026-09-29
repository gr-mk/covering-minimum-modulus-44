import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local11 : LocalData where
  prime := 11
  depth := 1
  rays := [⟨11, 1, 0, 1⟩, ⟨11, 1, 0, 2⟩, ⟨11, 1, 0, 3⟩, ⟨11, 1, 0, 4⟩, ⟨11, 1, 0, 5⟩, ⟨11, 1, 0, 6⟩, ⟨11, 1, 0, 7⟩, ⟨11, 1, 0, 8⟩, ⟨11, 1, 0, 9⟩, ⟨11, 1, 0, 10⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

def local11Centers : List ℤ := [0]
def local11Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def masks11 : List ℕ := [0x3ff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200]

theorem local11_samples_eq : compactCanonicalRepresentatives 11 1 local11.rays local11Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 22, 33, 44, 55, 66, 77, 88, 99, 110] := by decide

theorem local11_valid : local11.Valid := by
  apply LocalData.valid_of_compactWitnesses local11 local11Centers local11Witnesses
  · decide
  · decide
  · change local11.SignatureWitnessesValid (compactCanonicalRepresentatives 11 1 local11.rays
      local11Centers) local11Witnesses
    rw [local11_samples_eq]
    decide

theorem masks11_ok : ∀ k < local11.coordinates.length, masks11.getD k 0 =
    (local11.coordinates.getD k (.fixed 0 0)).mask 11 local11.representatives := by decide +kernel

end UC85.W.U
