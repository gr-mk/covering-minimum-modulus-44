import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local17 : LocalData where
  prime := 17
  depth := 1
  rays := [⟨17, 1, 0, 3⟩, ⟨17, 1, 0, 1⟩, ⟨17, 1, 0, 9⟩, ⟨17, 1, 0, 4⟩, ⟨17, 1, 0, 11⟩, ⟨17, 1, 0, 2⟩, ⟨17, 1, 0, 7⟩, ⟨17, 1, 0, 13⟩, ⟨17, 1, 0, 5⟩, ⟨17, 1, 0, 15⟩, ⟨17, 1, 0, 10⟩, ⟨17, 1, 0, 6⟩, ⟨17, 1, 0, 12⟩, ⟨17, 1, 0, 8⟩, ⟨17, 1, 0, 14⟩, ⟨17, 1, 0, 16⟩]
  coordinates := [.fixed 0 0, .ray 1 0 3, .ray 1 0 1, .ray 1 0 9, .ray 1 0 4, .ray 1 0 11, .ray 1 0 2, .ray 1 0 7, .ray 1 0 13, .ray 1 0 5, .ray 1 0 15, .ray 1 0 10, .ray 1 0 6, .ray 1 0 12, .ray 1 0 8, .ray 1 0 14, .ray 1 0 16]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

def local17Centers : List ℤ := [0]
def local17Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def masks17 : List ℕ := [0xffff, 0x4, 0x1, 0x100, 0x8, 0x400, 0x2, 0x40, 0x1000, 0x10, 0x4000, 0x200, 0x20, 0x800, 0x80, 0x2000, 0x8000]

theorem local17_samples_eq : compactCanonicalRepresentatives 17 1 local17.rays local17Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255, 272] := by decide

theorem local17_valid : local17.Valid := by
  apply LocalData.valid_of_compactWitnesses local17 local17Centers local17Witnesses
  · decide
  · decide
  · change local17.SignatureWitnessesValid (compactCanonicalRepresentatives 17 1 local17.rays
      local17Centers) local17Witnesses
    rw [local17_samples_eq]
    decide

theorem masks17_ok : ∀ k < local17.coordinates.length, masks17.getD k 0 =
    (local17.coordinates.getD k (.fixed 0 0)).mask 17 local17.representatives := by decide +kernel

end UC85.W.U
