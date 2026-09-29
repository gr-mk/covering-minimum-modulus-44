import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local3 : LocalData where
  prime := 3
  depth := 4
  rays := [⟨3, 1, 0, 2⟩, ⟨3, 3, 0, 1⟩, ⟨3, 2, 0, 2⟩, ⟨3, 3, 0, 2⟩, ⟨3, 4, (-6), 1⟩, ⟨3, 2, 0, 1⟩, ⟨3, 1, 0, 1⟩, ⟨3, 2, (-2), 1⟩, ⟨3, 2, (-2), 2⟩, ⟨3, 3, (-6), 2⟩, ⟨3, 4, (-24), 1⟩, ⟨3, 4, (-24), 2⟩, ⟨3, 2, (-1), 1⟩, ⟨3, 2, (-1), 2⟩, ⟨3, 3, (-3), 1⟩, ⟨3, 3, (-3), 2⟩, ⟨3, 2, 1, 1⟩, ⟨3, 2, 1, 2⟩]
  coordinates := [.fixed 0 0, .fixed 1 1, .fixed 3 13, .ray 1 0 2, .ray 3 0 1, .ray 2 0 2, .ray 3 0 2, .ray 4 (-6) 1, .ray 2 0 1, .fixed 1 2, .ray 1 0 1, .ray 2 (-2) 1, .ray 2 (-2) 2, .fixed 2 6, .fixed 3 3, .ray 3 (-6) 2, .fixed 2 3, .fixed 2 1, .fixed 2 4, .fixed 2 7, .ray 4 (-24) 1, .ray 4 (-24) 2, .ray 2 (-1) 1, .ray 2 (-1) 2, .fixed 1 0, .ray 3 (-3) 1, .ray 3 (-3) 2, .ray 2 1 1, .ray 2 1 2]
  representatives := [2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 30]

def local3Centers : List ℤ := [0, (-6), (-2), (-24), (-1), (-3), 1]
def local3Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 0, 6, 7, 0, 8, 9, 3, 10, 11, 3, 12, 13, 0, 14, 2, 3, 4, 5, 0, 6, 7, 0, 15, 2, 3, 4, 5, 0, 6, 7, 0, 8, 9, 3, 10, 11, 3, 12, 13, 0, 8, 2, 3, 10, 11, 3, 12, 13, 0, 2, 3, 4, 5, 0, 6, 7, 0, 8, 9, 3, 10, 11, 3, 12, 13, 0, 2, 3, 6, 12, 14, 8, 5, 11, 1, 15, 0, 3, 4, 10, 7, 13]
def masks3 : List ℕ := [0xffff, 0x2aa4, 0x200, 0x1419, 0x40, 0x1410, 0x1000, 0x4000, 0xc142, 0x9, 0xebe6, 0x20a0, 0xa04, 0x410, 0x8002, 0x100, 0xc102, 0x2080, 0x204, 0x820, 0x2, 0x8000, 0x1, 0x8, 0xd552, 0x10, 0x400, 0x284, 0x2820]

theorem local3_samples_eq : compactCanonicalRepresentatives 3 4 local3.rays local3Centers =
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 76, 77, 81, 162, 75, 156, 79, 160, 57, 138, 80, 161, 78, 159, 82, 163] := by decide

theorem local3_valid : local3.Valid := by
  apply LocalData.valid_of_compactWitnesses local3 local3Centers local3Witnesses
  · decide
  · decide
  · change local3.SignatureWitnessesValid (compactCanonicalRepresentatives 3 4 local3.rays
      local3Centers) local3Witnesses
    rw [local3_samples_eq]
    decide

theorem masks3_ok : ∀ k < local3.coordinates.length, masks3.getD k 0 =
    (local3.coordinates.getD k (.fixed 0 0)).mask 3 local3.representatives := by decide +kernel

end UC85.W.U
