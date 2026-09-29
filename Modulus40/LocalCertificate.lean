import Modulus40.FiniteReduction

/-!
# Finite local signature certificates

A local certificate records which rays appear at one prime, a separating depth,
and a finite list of representative integers. The finite signature comparison
is linked here to all integer inputs, including arbitrarily deep prime powers.
-/

namespace Modulus40

def Coordinate.AccountedFor (p depth : ℕ) (rays : List Ray) : Coordinate → Prop
  | .fixed exponent _ => exponent ≤ depth
  | .ray first center digit => Ray.mk p first center digit ∈ rays

instance (p depth : ℕ) (rays : List Ray) (s : Coordinate) :
    Decidable (s.AccountedFor p depth rays) := by
  cases s <;> simp only [Coordinate.AccountedFor] <;> infer_instance

/-- A ray signature together with the residue at the separating depth determines
all coordinates accounted for by that signature. -/
theorem Coordinate.matches_iff_of_signature {p depth : ℕ} {rays : List Ray}
    (s : Coordinate) (hs : s.AccountedFor p depth rays) {z w : ℤ}
    (hmod : Int.ModEq (p ^ depth : ℕ) z w)
    (hray : ∀ r ∈ rays, r.Matches z ↔ r.Matches w) :
    s.Matches p z ↔ s.Matches p w := by
  cases s with
  | fixed exponent residue =>
    rw [Coordinate.matches_fixed, Coordinate.matches_fixed]
    have hsmall : Int.ModEq (p ^ exponent : ℕ) z w :=
      hmod.of_dvd (by exact_mod_cast pow_dvd_pow p hs)
    change Int.ModEq (p ^ exponent : ℕ) z residue ↔
      Int.ModEq (p ^ exponent : ℕ) w residue
    exact ⟨fun h => hsmall.symm.trans h, fun h => hsmall.trans h⟩
  | ray first center digit =>
    rw [Coordinate.matches_ray, Coordinate.matches_ray]
    exact hray _ hs

/-- Local representatives contain a signature for every noncentral integer. -/
theorem local_signature_realization {p depth : ℕ} (hp : p.Prime)
    (rays : List Ray) (coordinates : List Coordinate) (representatives : List ℤ)
    (hbase : ∀ r ∈ rays, r.base = p)
    (hfirst : ∀ r ∈ rays, 1 ≤ r.first ∧ r.first ≤ depth + 1)
    (hdigit : ∀ r ∈ rays, 1 ≤ r.digit ∧ r.digit < p)
    (hsep : ∀ r ∈ rays, ∀ s ∈ rays,
      Int.ModEq (p ^ depth : ℕ) r.center s.center → r.center = s.center)
    (haccount : ∀ s ∈ coordinates, s.AccountedFor p depth rays)
    (hgood : ∀ s ∈ coordinates, s.WellFormed p)
    (hfinite : ∀ w ∈ canonicalRepresentatives p depth rays,
      ∃ a ∈ representatives, ∀ s ∈ coordinates, s.test p w = s.test p a)
    (z : ℤ) (hz : ∀ r ∈ rays, z ≠ r.center) :
    ∃ a ∈ representatives, ∀ s ∈ coordinates, s.Matches p z ↔ s.Matches p a := by
  obtain ⟨w, hw, hmod, hsig⟩ :=
    exists_canonicalRepresentative hp rays hbase hfirst hdigit hsep z hz
  obtain ⟨a, ha, htest⟩ := hfinite w hw
  refine ⟨a, ha, ?_⟩
  intro s hs
  rw [s.matches_iff_of_signature (haccount s hs) hmod hsig]
  rw [← s.test_eq_true_iff hp (hgood s hs), ← s.test_eq_true_iff hp (hgood s hs)]
  exact congrArg (· = true) (htest s hs) |>.to_iff

end Modulus40
