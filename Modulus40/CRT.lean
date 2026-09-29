import Modulus40.Basic
import Mathlib.Data.Nat.ChineseRemainder

/-!
# Combining congruences with relatively prime moduli

A finite conjunction of congruences with positive, pairwise relatively prime
moduli is one congruence whose modulus is their product. Residues and tested
integers may be negative.
-/

namespace Modulus40

/-- Integer congruence modulo a product of pairwise relatively prime natural
moduli is equivalent to congruence modulo every factor. -/
theorem intModEq_list_map_prod_iff {ι : Type*} {a b : ℤ} {s : ι → ℕ}
    {cs : List ι} (hcoprime : cs.Pairwise (fun c d => Nat.Coprime (s c) (s d))) :
    Int.ModEq ((cs.map s).prod : ℤ) a b ↔
      ∀ c ∈ cs, Int.ModEq (s c : ℤ) a b := by
  induction cs with
  | nil => simp [Int.modEq_one]
  | cons c cs ih =>
    have hhead : Nat.Coprime (s c) (cs.map s).prod := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro n hn
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hn
      exact (List.pairwise_cons.mp hcoprime).1 d hd
    have hhead' : Int.natAbs (s c : ℤ) |>.Coprime
        (Int.natAbs ((cs.map s).prod : ℤ)) := by
      simpa only [Int.natAbs_natCast] using hhead
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul,
      ← Int.modEq_and_modEq_iff_modEq_mul hhead',
      ih hcoprime.of_cons, List.mem_cons, forall_eq_or_imp]

/-- Construct the unique residue modulo the product satisfying all factors. -/
def combineCongruences (cs : List Congruence)
    (hcoprime : cs.Pairwise (fun c d => Nat.Coprime c.modulus d.modulus)) : Congruence :=
  ⟨(cs.map Congruence.modulus).prod,
   (Nat.chineseRemainderOfList (fun c => (c.residue % (c.modulus : ℤ)).toNat)
     Congruence.modulus cs hcoprime).val⟩

@[simp] theorem combineCongruences_modulus (cs : List Congruence)
    (hcoprime : cs.Pairwise (fun c d => Nat.Coprime c.modulus d.modulus)) :
    (combineCongruences cs hcoprime).modulus = (cs.map Congruence.modulus).prod := rfl

/-- The residue constructed by CRT lies in every input congruence. -/
theorem combineCongruences_residue_covers (cs : List Congruence)
    (hcoprime : cs.Pairwise (fun c d => Nat.Coprime c.modulus d.modulus))
    (hpos : ∀ c ∈ cs, 0 < c.modulus) :
    ∀ c ∈ cs, c.Covers (combineCongruences cs hcoprime).residue := by
  intro c hc
  have h := (Nat.chineseRemainderOfList
    (fun c => (c.residue % (c.modulus : ℤ)).toNat)
    Congruence.modulus cs hcoprime).property c hc
  have hz : (0 : ℤ) < c.modulus := by exact_mod_cast hpos c hc
  have hn : 0 ≤ c.residue % (c.modulus : ℤ) :=
    Int.emod_nonneg _ (ne_of_gt hz)
  have hcast := Int.natCast_modEq_iff.mpr h
  rw [Int.toNat_of_nonneg hn] at hcast
  exact hcast.trans (Int.mod_modEq c.residue c.modulus)

/-- CRT realizes a finite intersection as a single congruence, for all integers. -/
theorem combineCongruences_covers_iff (cs : List Congruence)
    (hcoprime : cs.Pairwise (fun c d => Nat.Coprime c.modulus d.modulus))
    (hpos : ∀ c ∈ cs, 0 < c.modulus) (z : ℤ) :
    (combineCongruences cs hcoprime).Covers z ↔ ∀ c ∈ cs, c.Covers z := by
  change Int.ModEq ((cs.map Congruence.modulus).prod : ℤ) z
    (combineCongruences cs hcoprime).residue ↔ _
  rw [intModEq_list_map_prod_iff hcoprime]
  constructor
  · intro h c hc
    exact (h c hc).trans (combineCongruences_residue_covers cs hcoprime hpos c hc)
  · intro h c hc
    exact (h c hc).trans
      (combineCongruences_residue_covers cs hcoprime hpos c hc).symm

end Modulus40
