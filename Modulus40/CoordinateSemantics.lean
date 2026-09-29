import Modulus40.Coordinate
import Modulus40.Ray

/-!
# Arithmetic meaning of prime-coordinate certificates

Coordinate membership quantifies over the exponents in its support interval.
Truncation has a bounded witness whenever the tested integer is outside the
coordinate's tail. Fixed coordinates have no such exceptional tail.
-/

namespace Modulus40

def Coordinate.Matches (s : Coordinate) (p : ℕ) (z : ℤ) : Prop :=
  ∃ e : ℕ, s.interval.Contains e ∧ (s.at p e).Covers z

def Coordinate.InTail : Coordinate → ℕ → ℕ → ℤ → Prop
  | .fixed _ _, _, _, _ => False
  | .ray _ center _, p, bound, z => (Congruence.mk (p ^ bound) center).Covers z

@[simp] theorem Coordinate.matches_fixed (exponent p : ℕ) (residue z : ℤ) :
    (Coordinate.fixed exponent residue).Matches p z ↔
      (Congruence.mk (p ^ exponent) residue).Covers z := by
  simp [Coordinate.Matches, Coordinate.interval, Coordinate.at]

@[simp] theorem Coordinate.matches_ray (first p digit : ℕ) (center z : ℤ) :
    (Coordinate.ray first center digit).Matches p z ↔
      (Ray.mk p first center digit).Matches z := by
  simp [Coordinate.Matches, Coordinate.interval, Coordinate.at,
    Ray.Matches, Ray.at]

/-- Every match has a bounded exponent unless it lies in an arrow tail. -/
theorem Coordinate.bounded_witness {s : Coordinate} {p bound : ℕ} {z : ℤ}
    (hlo : s.interval.lo ≤ bound)
    (h : s.Matches p z) (ht : ¬ s.InTail p bound z) :
    ∃ e : ℕ, s.interval.Contains e ∧ e ≤ bound ∧ (s.at p e).Covers z := by
  cases s with
  | fixed e a =>
    refine ⟨e, by simp [Coordinate.interval], hlo, ?_⟩
    exact (Coordinate.matches_fixed e p a z).mp h
  | ray first center digit =>
    have hr : (Ray.mk p first center digit).Matches z :=
      (Coordinate.matches_ray first p digit center z).mp h
    have hrt : ¬ ((Ray.mk p first center digit).tail bound).Covers z := ht
    obtain ⟨e, he, heb, hez⟩ := Ray.bounded_witness hrt hr
    exact ⟨e, by simpa [Coordinate.interval] using he, heb, hez⟩

def PrimePattern.Matches {d : ℕ} (pattern : PrimePattern d)
    (primes : Fin d → ℕ) (z : ℤ) : Prop :=
  ∀ i, (pattern i).Matches (primes i) z

def PrimePattern.InTail {d : ℕ} (pattern : PrimePattern d)
    (primes : Fin d → ℕ) (bound : ℕ) (z : ℤ) : Prop :=
  ∃ i, (pattern i).InTail (primes i) bound z

/-- All coordinates of one symbolic pattern can be realized simultaneously
inside the finite exponent cube. -/
theorem PrimePattern.bounded_witness {d : ℕ} {pattern : PrimePattern d}
    {primes : Fin d → ℕ} {bound : ℕ} {z : ℤ}
    (hlo : ∀ i, (pattern i).interval.lo ≤ bound)
    (h : pattern.Matches primes z) (ht : ¬ pattern.InTail primes bound z) :
    ∃ e : Fin d → Fin (bound + 1), ∀ i,
      (pattern i).interval.Contains (e i).val ∧
      ((pattern i).at (primes i) (e i).val).Covers z := by
  have hw : ∀ i, ∃ e : ℕ, (pattern i).interval.Contains e ∧ e ≤ bound ∧
      ((pattern i).at (primes i) e).Covers z := by
    intro i
    exact Coordinate.bounded_witness (hlo i) (h i) (fun h' => ht ⟨i, h'⟩)
  choose e he hb hz using hw
  exact ⟨fun i => ⟨e i, by have := hb i; omega⟩, fun i => ⟨he i, hz i⟩⟩

end Modulus40
