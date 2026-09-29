import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local13 : LocalData where
  prime := 13
  depth := 1
  rays := [⟨13, 1, 0, 1⟩, ⟨13, 1, 0, 2⟩, ⟨13, 1, 0, 3⟩, ⟨13, 1, 0, 4⟩, ⟨13, 1, 0, 5⟩, ⟨13, 1, 0, 6⟩, ⟨13, 1, 0, 7⟩, ⟨13, 1, 0, 8⟩, ⟨13, 1, 0, 9⟩, ⟨13, 1, 0, 10⟩, ⟨13, 1, 0, 11⟩, ⟨13, 1, 0, 12⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def local13Centers : List ℤ := [0]
def local13Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
def masks13 : List ℕ := [0xfff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800]

theorem local13_samples_eq : compactCanonicalRepresentatives 13 1 local13.rays local13Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 26, 39, 52, 65, 78, 91, 104, 117, 130, 143, 156] := by decide

theorem local13_valid : local13.Valid := by
  apply LocalData.valid_of_compactWitnesses local13 local13Centers local13Witnesses
  · decide
  · decide
  · change local13.SignatureWitnessesValid (compactCanonicalRepresentatives 13 1 local13.rays
      local13Centers) local13Witnesses
    rw [local13_samples_eq]
    decide

theorem masks13_ok : ∀ k < local13.coordinates.length, masks13.getD k 0 =
    (local13.coordinates.getD k (.fixed 0 0)).mask 13 local13.representatives := by decide +kernel

end UC85.W.U
