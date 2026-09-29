import Modulus40.Support

/-!
# Prime coordinates for the finite certificate

Each coordinate records a fixed prime-power class or one arrow ray, together
with the corresponding interval of admissible exponents.
-/

namespace Modulus40

inductive Coordinate where
  | fixed (exponent : ℕ) (residue : ℤ)
  | ray (first : ℕ) (center : ℤ) (digit : ℕ)
  deriving DecidableEq, Repr

def Coordinate.interval : Coordinate → SupportInterval
  | .fixed exponent _ => .fixed exponent
  | .ray first _ _ => .ray first

/-- The exponent is explicit, and its admissibility is checked separately. -/
def Coordinate.at (s : Coordinate) (p e : ℕ) : Congruence where
  modulus := p ^ e
  residue := match s with
    | .fixed _ residue => residue
    | .ray _ center digit => center + (digit : ℤ) * (p : ℤ) ^ (e - 1)

@[simp] theorem Coordinate.at_modulus (s : Coordinate) (p e : ℕ) :
    (s.at p e).modulus = p ^ e := rfl

abbrev PrimePattern (d : ℕ) := Fin d → Coordinate

def primePatternBoxes {d k : ℕ} (patterns : Fin k → PrimePattern d) :
    Fin k → SupportBox d :=
  fun i j => (patterns i j).interval

end Modulus40
