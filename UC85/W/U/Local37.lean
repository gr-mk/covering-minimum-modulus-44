import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local37 : LocalData where
  prime := 37
  depth := 1
  rays := [⟨37, 1, 0, 1⟩, ⟨37, 1, 0, 2⟩, ⟨37, 1, 0, 3⟩, ⟨37, 1, 0, 4⟩, ⟨37, 1, 0, 5⟩, ⟨37, 1, 0, 6⟩, ⟨37, 1, 0, 7⟩, ⟨37, 1, 0, 8⟩, ⟨37, 1, 0, 9⟩, ⟨37, 1, 0, 10⟩, ⟨37, 1, 0, 11⟩, ⟨37, 1, 0, 12⟩, ⟨37, 1, 0, 13⟩, ⟨37, 1, 0, 14⟩, ⟨37, 1, 0, 15⟩, ⟨37, 1, 0, 16⟩, ⟨37, 1, 0, 17⟩, ⟨37, 1, 0, 18⟩, ⟨37, 1, 0, 19⟩, ⟨37, 1, 0, 20⟩, ⟨37, 1, 0, 21⟩, ⟨37, 1, 0, 22⟩, ⟨37, 1, 0, 23⟩, ⟨37, 1, 0, 24⟩, ⟨37, 1, 0, 25⟩, ⟨37, 1, 0, 26⟩, ⟨37, 1, 0, 27⟩, ⟨37, 1, 0, 28⟩, ⟨37, 1, 0, 29⟩, ⟨37, 1, 0, 30⟩, ⟨37, 1, 0, 31⟩, ⟨37, 1, 0, 32⟩, ⟨37, 1, 0, 33⟩, ⟨37, 1, 0, 34⟩, ⟨37, 1, 0, 35⟩, ⟨37, 1, 0, 36⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18, .ray 1 0 19, .ray 1 0 20, .ray 1 0 21, .ray 1 0 22, .ray 1 0 23, .ray 1 0 24, .ray 1 0 25, .ray 1 0 26, .ray 1 0 27, .ray 1 0 28, .ray 1 0 29, .ray 1 0 30, .ray 1 0 31, .ray 1 0 32, .ray 1 0 33, .ray 1 0 34, .ray 1 0 35, .ray 1 0 36]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]

def local37Centers : List ℤ := [0]
def local37Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35]
def masks37 : List ℕ := [0xfffffffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000, 0x8000000, 0x10000000, 0x20000000, 0x40000000, 0x80000000, 0x100000000, 0x200000000, 0x400000000, 0x800000000]

theorem local37_samples_eq : compactCanonicalRepresentatives 37 1 local37.rays local37Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 74, 111, 148, 185, 222, 259, 296, 333, 370, 407, 444, 481, 518, 555, 592, 629, 666, 703, 740, 777, 814, 851, 888, 925, 962, 999, 1036, 1073, 1110, 1147, 1184, 1221, 1258, 1295, 1332] := by decide

theorem local37_valid : local37.Valid := by
  apply LocalData.valid_of_compactWitnesses local37 local37Centers local37Witnesses
  · decide
  · decide
  · change local37.SignatureWitnessesValid (compactCanonicalRepresentatives 37 1 local37.rays
      local37Centers) local37Witnesses
    rw [local37_samples_eq]
    decide

theorem masks37_ok : ∀ k < local37.coordinates.length, masks37.getD k 0 =
    (local37.coordinates.getD k (.fixed 0 0)).mask 37 local37.representatives := by decide +kernel

end UC85.W.U
