import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local23 : LocalData where
  prime := 23
  depth := 1
  rays := [⟨23, 1, 0, 1⟩, ⟨23, 1, 0, 2⟩, ⟨23, 1, 0, 3⟩, ⟨23, 1, 0, 4⟩, ⟨23, 1, 0, 5⟩, ⟨23, 1, 0, 6⟩, ⟨23, 1, 0, 7⟩, ⟨23, 1, 0, 8⟩, ⟨23, 1, 0, 9⟩, ⟨23, 1, 0, 10⟩, ⟨23, 1, 0, 11⟩, ⟨23, 1, 0, 12⟩, ⟨23, 1, 0, 13⟩, ⟨23, 1, 0, 14⟩, ⟨23, 1, 0, 15⟩, ⟨23, 1, 0, 16⟩, ⟨23, 1, 0, 17⟩, ⟨23, 1, 0, 18⟩, ⟨23, 1, 0, 19⟩, ⟨23, 1, 0, 20⟩, ⟨23, 1, 0, 21⟩, ⟨23, 1, 0, 22⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18, .ray 1 0 19, .ray 1 0 20, .ray 1 0 21, .ray 1 0 22]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

def local23Centers : List ℤ := [0]
def local23Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]
def masks23 : List ℕ := [0x3fffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000]

theorem local23_samples_eq : compactCanonicalRepresentatives 23 1 local23.rays local23Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 46, 69, 92, 115, 138, 161, 184, 207, 230, 253, 276, 299, 322, 345, 368, 391, 414, 437, 460, 483, 506] := by decide

theorem local23_valid : local23.Valid := by
  apply LocalData.valid_of_compactWitnesses local23 local23Centers local23Witnesses
  · decide
  · decide
  · change local23.SignatureWitnessesValid (compactCanonicalRepresentatives 23 1 local23.rays
      local23Centers) local23Witnesses
    rw [local23_samples_eq]
    decide

theorem masks23_ok : ∀ k < local23.coordinates.length, masks23.getD k 0 =
    (local23.coordinates.getD k (.fixed 0 0)).mask 23 local23.representatives := by decide +kernel

end UC85.W.U
