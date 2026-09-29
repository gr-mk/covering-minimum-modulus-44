import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local7 : LocalData where
  prime := 7
  depth := 2
  rays := [⟨7, 2, (-4), 1⟩, ⟨7, 2, (-4), 2⟩, ⟨7, 2, (-4), 3⟩, ⟨7, 2, (-4), 4⟩, ⟨7, 2, (-4), 5⟩, ⟨7, 2, (-4), 6⟩, ⟨7, 1, 0, 1⟩, ⟨7, 1, 0, 2⟩, ⟨7, 2, 0, 3⟩, ⟨7, 1, 0, 3⟩, ⟨7, 1, 0, 4⟩, ⟨7, 1, 0, 5⟩, ⟨7, 1, 0, 6⟩]
  coordinates := [.fixed 0 0, .ray 2 (-4) 1, .ray 2 (-4) 2, .ray 2 (-4) 3, .ray 2 (-4) 4, .ray 2 (-4) 5, .ray 2 (-4) 6, .ray 1 0 1, .ray 1 0 2, .ray 2 0 3, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .fixed 1 3]
  representatives := [1, 2, 3, 4, 5, 6, 10, 17, 21, 24, 31, 38]

def local7Centers : List ℤ := [(-4), 0]
def local7Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 0, 0, 1, 6, 3, 4, 5, 1, 0, 1, 7, 3, 4, 5, 8, 0, 1, 9, 3, 4, 5, 3, 0, 1, 10, 3, 4, 5, 4, 0, 1, 11, 3, 4, 5, 5, 0, 1, 3, 4, 5, 2, 6, 7, 9, 10, 11, 0, 1, 8, 3, 4, 5]
def masks7 : List ℕ := [0xfff, 0x4, 0x40, 0x80, 0x200, 0x400, 0x800, 0x1, 0x2, 0x100, 0xfc4, 0x8, 0x10, 0x20, 0xec4]

theorem local7_samples_eq : compactCanonicalRepresentatives 7 2 local7.rays local7Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 45, 94, 143, 192, 241, 290, 49, 98, 147, 196, 245, 294] := by decide

theorem local7_valid : local7.Valid := by
  apply LocalData.valid_of_compactWitnesses local7 local7Centers local7Witnesses
  · decide
  · decide
  · change local7.SignatureWitnessesValid (compactCanonicalRepresentatives 7 2 local7.rays
      local7Centers) local7Witnesses
    rw [local7_samples_eq]
    decide

theorem masks7_ok : ∀ k < local7.coordinates.length, masks7.getD k 0 =
    (local7.coordinates.getD k (.fixed 0 0)).mask 7 local7.representatives := by decide +kernel

end UC85.W.U
