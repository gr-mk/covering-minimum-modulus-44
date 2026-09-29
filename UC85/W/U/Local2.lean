import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local2 : LocalData where
  prime := 2
  depth := 6
  rays := [⟨2, 6, 0, 1⟩, ⟨2, 4, (-1), 1⟩, ⟨2, 5, (-8), 1⟩, ⟨2, 6, (-16), 1⟩, ⟨2, 2, 0, 1⟩, ⟨2, 4, (-4), 1⟩, ⟨2, 3, (-2), 1⟩, ⟨2, 3, (-3), 1⟩, ⟨2, 3, (-1), 1⟩, ⟨2, 4, (-5), 1⟩, ⟨2, 4, 12, 1⟩, ⟨2, 3, 2, 1⟩, ⟨2, 4, (-6), 1⟩, ⟨2, 4, (-2), 1⟩, ⟨2, 4, 6, 1⟩, ⟨2, 3, 266, 1⟩, ⟨2, 3, 182, 1⟩, ⟨2, 4, 2, 1⟩, ⟨2, 4, 4, 1⟩, ⟨2, 5, 8, 1⟩, ⟨2, 6, 16, 1⟩]
  coordinates := [.fixed 0 0, .ray 6 0 1, .fixed 1 0, .fixed 2 0, .fixed 5 24, .ray 4 (-1) 1, .fixed 1 1, .fixed 3 3, .fixed 2 1, .fixed 4 8, .fixed 5 16, .fixed 2 2, .fixed 3 4, .ray 5 (-8) 1, .ray 6 (-16) 1, .ray 2 0 1, .ray 4 (-4) 1, .ray 3 (-2) 1, .ray 3 (-3) 1, .fixed 2 3, .ray 3 (-1) 1, .ray 4 (-5) 1, .ray 4 12 1, .ray 3 2 1, .fixed 3 2, .ray 4 (-6) 1, .fixed 3 6, .ray 4 (-2) 1, .ray 4 6 1, .fixed 3 0, .fixed 4 0, .ray 3 266 1, .ray 3 182 1, .ray 4 2 1, .ray 4 4 1, .ray 5 8 1, .ray 6 16 1, .fixed 2 262, .fixed 2 178]
  representatives := [1, 3, 7, 14, 18, 20, 24, 32, 40, 48]

def local2Centers : List ℤ := [0, (-1), (-8), (-16), (-4), (-2), (-3), (-5), 12, 2, (-6), 6, 266, 182, 4, 8, 16]
def local2Witnesses : List ℕ := [0, 1, 0, 2, 0, 1, 0, 3, 2, 0, 4, 1, 5, 0, 3, 2, 6, 0, 4, 1, 5, 0, 3, 2, 7, 0, 4, 1, 5, 0, 3, 2, 8, 0, 4, 1, 5, 0, 3, 2, 0, 4, 1, 5, 0, 2, 0, 7, 2, 6, 9, 5, 3, 0, 1, 5, 4, 4, 3, 4, 3, 5, 8, 9]
def masks2 : List ℕ := [0x3ff, 0x80, 0x3f8, 0x3e0, 0x40, 0x4, 0x7, 0x2, 0x1, 0x140, 0x200, 0x18, 0x20, 0x140, 0x200, 0x3f8, 0x20, 0x18, 0x1, 0x6, 0x6, 0x2, 0x20, 0x18, 0x10, 0x10, 0x8, 0x8, 0x8, 0x3c0, 0x280, 0x18, 0x18, 0x10, 0x20, 0x140, 0x200, 0x18, 0x18]

theorem local2_samples_eq : compactCanonicalRepresentatives 2 6 local2.rays local2Centers =
    [1, 3, 5, 7, 9, 11, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 49, 50, 51, 52, 53, 55, 57, 64, 63, 56, 48, 60, 62, 61, 59, 76, 66, 58, 70, 330, 246, 68, 72, 80] := by decide

theorem local2_valid : local2.Valid := by
  apply LocalData.valid_of_compactWitnesses local2 local2Centers local2Witnesses
  · decide
  · decide
  · change local2.SignatureWitnessesValid (compactCanonicalRepresentatives 2 6 local2.rays
      local2Centers) local2Witnesses
    rw [local2_samples_eq]
    decide

theorem masks2_ok : ∀ k < local2.coordinates.length, masks2.getD k 0 =
    (local2.coordinates.getD k (.fixed 0 0)).mask 2 local2.representatives := by decide +kernel

end UC85.W.U
