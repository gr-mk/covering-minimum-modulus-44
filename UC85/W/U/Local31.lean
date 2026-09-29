import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local31 : LocalData where
  prime := 31
  depth := 1
  rays := [⟨31, 1, 0, 1⟩, ⟨31, 1, 0, 2⟩, ⟨31, 1, 0, 3⟩, ⟨31, 1, 0, 4⟩, ⟨31, 1, 0, 5⟩, ⟨31, 1, 0, 6⟩, ⟨31, 1, 0, 7⟩, ⟨31, 1, 0, 8⟩, ⟨31, 1, 0, 9⟩, ⟨31, 1, 0, 10⟩, ⟨31, 1, 0, 11⟩, ⟨31, 1, 0, 12⟩, ⟨31, 1, 0, 13⟩, ⟨31, 1, 0, 14⟩, ⟨31, 1, 0, 15⟩, ⟨31, 1, 0, 16⟩, ⟨31, 1, 0, 17⟩, ⟨31, 1, 0, 18⟩, ⟨31, 1, 0, 19⟩, ⟨31, 1, 0, 20⟩, ⟨31, 1, 0, 21⟩, ⟨31, 1, 0, 22⟩, ⟨31, 1, 0, 23⟩, ⟨31, 1, 0, 24⟩, ⟨31, 1, 0, 25⟩, ⟨31, 1, 0, 26⟩, ⟨31, 1, 0, 27⟩, ⟨31, 1, 0, 28⟩, ⟨31, 1, 0, 29⟩, ⟨31, 1, 0, 30⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18, .ray 1 0 19, .ray 1 0 20, .ray 1 0 21, .ray 1 0 22, .ray 1 0 23, .ray 1 0 24, .ray 1 0 25, .ray 1 0 26, .ray 1 0 27, .ray 1 0 28, .ray 1 0 29, .ray 1 0 30]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]

def local31Centers : List ℤ := [0]
def local31Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29]
def masks31 : List ℕ := [0x3fffffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000, 0x8000000, 0x10000000, 0x20000000]

theorem local31_samples_eq : compactCanonicalRepresentatives 31 1 local31.rays local31Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 62, 93, 124, 155, 186, 217, 248, 279, 310, 341, 372, 403, 434, 465, 496, 527, 558, 589, 620, 651, 682, 713, 744, 775, 806, 837, 868, 899, 930] := by decide

theorem local31_valid : local31.Valid := by
  apply LocalData.valid_of_compactWitnesses local31 local31Centers local31Witnesses
  · decide
  · decide
  · change local31.SignatureWitnessesValid (compactCanonicalRepresentatives 31 1 local31.rays
      local31Centers) local31Witnesses
    rw [local31_samples_eq]
    decide

theorem masks31_ok : ∀ k < local31.coordinates.length, masks31.getD k 0 =
    (local31.coordinates.getD k (.fixed 0 0)).mask 31 local31.representatives := by decide +kernel

end UC85.W.U
