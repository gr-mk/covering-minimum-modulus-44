import UC85.Glue
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UC85.W.U
open Modulus40

def local19 : LocalData where
  prime := 19
  depth := 1
  rays := [⟨19, 1, 0, 1⟩, ⟨19, 1, 0, 2⟩, ⟨19, 1, 0, 3⟩, ⟨19, 1, 0, 4⟩, ⟨19, 1, 0, 5⟩, ⟨19, 1, 0, 6⟩, ⟨19, 1, 0, 7⟩, ⟨19, 1, 0, 8⟩, ⟨19, 1, 0, 9⟩, ⟨19, 1, 0, 10⟩, ⟨19, 1, 0, 11⟩, ⟨19, 1, 0, 12⟩, ⟨19, 1, 0, 13⟩, ⟨19, 1, 0, 14⟩, ⟨19, 1, 0, 15⟩, ⟨19, 1, 0, 16⟩, ⟨19, 1, 0, 17⟩, ⟨19, 1, 0, 18⟩]
  coordinates := [.fixed 0 0, .ray 1 0 1, .ray 1 0 2, .ray 1 0 3, .ray 1 0 4, .ray 1 0 5, .ray 1 0 6, .ray 1 0 7, .ray 1 0 8, .ray 1 0 9, .ray 1 0 10, .ray 1 0 11, .ray 1 0 12, .ray 1 0 13, .ray 1 0 14, .ray 1 0 15, .ray 1 0 16, .ray 1 0 17, .ray 1 0 18]
  representatives := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

def local19Centers : List ℤ := [0]
def local19Witnesses : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
def masks19 : List ℕ := [0x3ffff, 0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000, 0x10000, 0x20000]

theorem local19_samples_eq : compactCanonicalRepresentatives 19 1 local19.rays local19Centers =
    [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 38, 57, 76, 95, 114, 133, 152, 171, 190, 209, 228, 247, 266, 285, 304, 323, 342] := by decide

theorem local19_valid : local19.Valid := by
  apply LocalData.valid_of_compactWitnesses local19 local19Centers local19Witnesses
  · decide
  · decide
  · change local19.SignatureWitnessesValid (compactCanonicalRepresentatives 19 1 local19.rays
      local19Centers) local19Witnesses
    rw [local19_samples_eq]
    decide

theorem masks19_ok : ∀ k < local19.coordinates.length, masks19.getD k 0 =
    (local19.coordinates.getD k (.fixed 0 0)).mask 19 local19.representatives := by decide +kernel

end UC85.W.U
