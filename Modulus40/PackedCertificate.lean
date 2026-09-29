import Mathlib.Data.List.Basic

/-! Compact natural-number encodings for finite, kernel-reducible data. -/
namespace Modulus40

/-- Read at most `fuel` little-endian base-`base` digits; zero ends the list.
The explicit recursor avoids a course-of-values table proportional to the fuel. -/
def unpackDigits (base fuel value : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ recur n => if n = 0 then [] else (n % base) :: recur (n / base)) fuel value

/-- The positive/negative literal encoding uses its low bit as polarity. -/
def unpackClause (value : Nat) : List (Nat × Bool) :=
  (unpackDigits 32768 512 value).map (fun digit => (digit / 2, digit % 2 == 1))

/-- Hints store the clause index plus one so that index zero is representable. -/
def unpackHints (value : Nat) : List Nat :=
  (unpackDigits 131072 512 value).map (· - 1)

end Modulus40
