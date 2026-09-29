import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local29 : LocalData where
  prime := 29
  depth := 1
  rays := [⟨29, 1, 0, 1⟩, ⟨29, 1, 0, 2⟩, ⟨29, 1, 0, 3⟩, ⟨29, 1, 0, 4⟩, ⟨29, 1, 0, 5⟩, ⟨29, 1, 0, 6⟩, ⟨29, 1, 0, 7⟩, ⟨29, 1, 0, 8⟩, ⟨29, 1, 0, 9⟩, ⟨29, 1, 0, 10⟩, ⟨29, 1, 0, 11⟩, ⟨29, 1, 0, 12⟩, ⟨29, 1, 0, 13⟩, ⟨29, 1, 0, 14⟩, ⟨29, 1, 0, 15⟩, ⟨29, 1, 0, 16⟩, ⟨29, 1, 0, 17⟩, ⟨29, 1, 0, 18⟩, ⟨29, 1, 0, 19⟩, ⟨29, 1, 0, 20⟩, ⟨29, 1, 0, 21⟩, ⟨29, 1, 0, 22⟩, ⟨29, 1, 0, 23⟩, ⟨29, 1, 0, 24⟩, ⟨29, 1, 0, 25⟩, ⟨29, 1, 0, 26⟩, ⟨29, 1, 0, 27⟩, ⟨29, 1, 0, 28⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18, .ray 1 0 19, .ray 1 0 20, .ray 1 0 21, .ray 1 0 22, .ray 1 0 23, .ray 1 0 24, .ray 1 0 25, .ray 1 0 26, .ray 1 0 27, .ray 1 0 28]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

def local29Centers : List ℤ := [0]
def local29Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
def masks29 : List ℕ := [0xfffffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000, 0x8000000]

theorem local29_samples_eq : compactCanonicalRepresentatives 29 1 local29.rays local29Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 58, 87, 116, 145, 174, 203, 232, 261, 290, 319, 348, 377, 406, 435, 464, 493, 522, 551, 580, 609, 638, 667, 696, 725, 754, 783, 812] := by decide

theorem local29_valid : local29.Valid := by
  apply LocalData.valid_of_compactWitnesses local29 local29Centers local29Witnesses
  · decide
  · decide
  · change local29.SignatureWitnessesValid (compactCanonicalRepresentatives 29 1 local29.rays
      local29Centers) local29Witnesses
    rw [local29_samples_eq]
    decide

theorem masks29_ok : ∀ k < local29.coordinates.length, masks29.getD k 0 =
    (local29.coordinates.getD k (.fixed 0 0)).mask 29 local29.representatives := by decide +kernel

end UC85.W.U
