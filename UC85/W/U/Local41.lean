import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local41 : LocalData where
  prime := 41
  depth := 1
  rays := [⟨41, 1, 0, 1⟩, ⟨41, 1, 0, 2⟩, ⟨41, 1, 0, 3⟩, ⟨41, 1, 0, 4⟩, ⟨41, 1, 0, 5⟩, ⟨41, 1, 0, 6⟩, ⟨41, 1, 0, 7⟩, ⟨41, 1, 0, 8⟩, ⟨41, 1, 0, 9⟩, ⟨41, 1, 0, 10⟩, ⟨41, 1, 0, 11⟩, ⟨41, 1, 0, 12⟩, ⟨41, 1, 0, 13⟩, ⟨41, 1, 0, 14⟩, ⟨41, 1, 0, 15⟩, ⟨41, 1, 0, 16⟩, ⟨41, 1, 0, 17⟩, ⟨41, 1, 0, 18⟩, ⟨41, 1, 0, 19⟩, ⟨41, 1, 0, 20⟩, ⟨41, 1, 0, 21⟩, ⟨41, 1, 0, 22⟩, ⟨41, 1, 0, 23⟩, ⟨41, 1, 0, 24⟩, ⟨41, 1, 0, 25⟩, ⟨41, 1, 0, 26⟩, ⟨41, 1, 0, 27⟩, ⟨41, 1, 0, 28⟩, ⟨41, 1, 0, 29⟩, ⟨41, 1, 0, 30⟩, ⟨41, 1, 0, 31⟩, ⟨41, 1, 0, 32⟩, ⟨41, 1, 0, 33⟩, ⟨41, 1, 0, 34⟩, ⟨41, 1, 0, 35⟩, ⟨41, 1, 0, 36⟩, ⟨41, 1, 0, 37⟩, ⟨41, 1, 0, 38⟩, ⟨41, 1, 0, 39⟩, ⟨41, 1, 0, 40⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18, .ray 1 0 19, .ray 1 0 20, .ray 1 0 21, .ray 1 0 22, .ray 1 0 23, .ray 1 0 24, .ray 1 0 25, .ray 1 0 26, .ray 1 0 27, .ray 1 0 28, .ray 1 0 29, .ray 1 0 30, .ray 1 0 31, .ray 1 0 32, .ray 1 0 33, .ray 1 0 34, .ray 1 0 35, .ray 1 0 36, .ray 1 0 37, .ray 1 0 38, .ray 1 0 39, .ray 1 0 40]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]

def local41Centers : List ℤ := [0]
def local41Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39]
def masks41 : List ℕ := [0xffffffffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000, 0x40000, 0x80000, 0x100000, 0x200000, 0x400000, 0x800000, 0x1000000, 0x2000000, 0x4000000, 0x8000000, 0x10000000, 0x20000000, 0x40000000, 0x80000000, 0x100000000, 0x200000000, 0x400000000, 0x800000000, 0x1000000000, 0x2000000000, 0x4000000000, 0x8000000000]

theorem local41_samples_eq : compactCanonicalRepresentatives 41 1 local41.rays local41Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 82, 123, 164, 205, 246, 287, 328, 369, 410, 451, 492, 533, 574, 615, 656, 697, 738, 779, 820, 861, 902, 943, 984, 1025, 1066, 1107, 1148, 1189, 1230, 1271, 1312, 1353, 1394, 1435, 1476, 1517, 1558, 1599, 1640] := by decide

theorem local41_valid : local41.Valid := by
  apply LocalData.valid_of_compactWitnesses local41 local41Centers local41Witnesses
  · decide
  · decide
  · change local41.SignatureWitnessesValid (compactCanonicalRepresentatives 41 1 local41.rays
      local41Centers) local41Witnesses
    rw [local41_samples_eq]
    decide

theorem masks41_ok : ∀ k < local41.coordinates.length, masks41.getD k 0 =
    (local41.coordinates.getD k (.fixed 0 0)).mask 41 local41.representatives := by decide +kernel

end UC85.W.U
