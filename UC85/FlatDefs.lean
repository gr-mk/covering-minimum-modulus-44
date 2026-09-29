import Modulus40.LocalDataChecking
import Modulus40.FastRUPCertificate
import Modulus40.PackedCertificate

/-!
# Flat selector-circuit certificates (UC85 pilot)

A section check is a CNF over exact local atoms: one variable per (prime, atom), a gate
variable per multi-atom coordinate mask, at-least-one clauses per prime, gate definitions
`g ∨ ¬v`, and one clause per family.  The kept original clauses of a RUP refutation carry
origin tags; `Env.originOK` checks each clause against its origin by kernel reduction.
`Env.cover` turns the refutation into coverage of the target pattern by the families,
away from the finitely many ray centers of the local tables.
-/

namespace UC85
open Modulus40

/-- What a CNF variable stands for. -/
inductive VarInfo (d : ℕ) where
  | atom (j : Fin d) (a : ℕ)
  | gate (j : Fin d) (m : ℕ)
  | unused

/-- The assignment induced by an atom choice `x`. -/
def VarInfo.eval {d : ℕ} (x : Fin d → ℕ) : VarInfo d → Bool
  | .atom j a => x j == a
  | .gate j m => m.testBit (x j)
  | .unused => false

/-- Why a kept original clause belongs to the CNF. -/
inductive Origin (d : ℕ) where
  | alo (j : Fin d)
  | gate
  | fam (i : ℕ)

/-- Hint lists of up to 2^20 clauses, stored as index plus one. -/
def unpackHints20 (value : ℕ) : List ℕ :=
  (unpackDigits 1048576 512 value).map (· - 1)

def decodeOrigin (d n : ℕ) : Origin d :=
  if n = 0 then .gate else if h : n - 1 < d then .alo ⟨n - 1, h⟩ else .fam (n - 1 - d)

/-- Every coordinate mask of prime `j` is the tested mask over its representatives. -/
def MasksValid {d : ℕ} (primes : Fin d → ℕ) (ld : Fin d → LocalData)
    (maskAt : Fin d → ℕ → ℕ) (j : Fin d) : Prop :=
  (ld j).prime = primes j ∧
  ∀ k < (ld j).coordinates.length,
    maskAt j k = ((ld j).coordinates.getD k (.fixed 0 0)).mask (primes j) (ld j).representatives

instance {d : ℕ} (primes : Fin d → ℕ) (ld : Fin d → LocalData) (maskAt : Fin d → ℕ → ℕ)
    (j : Fin d) : Decidable (MasksValid primes ld maskAt j) := by
  unfold MasksValid; infer_instance

structure Env (d : ℕ) where
  primes : Fin d → ℕ
  ld : Fin d → LocalData
  maskAt : Fin d → ℕ → ℕ
  tIdx : Fin d → ℕ
  famIdx : ℕ → Fin d → ℕ
  famCount : ℕ
  vinfo : ℕ → VarInfo d

namespace Env
variable {d : ℕ} (E : Env d)

def coord (j : Fin d) (k : ℕ) : Coordinate := (E.ld j).coordinates.getD k (.fixed 0 0)
def target : PrimePattern d := fun j => E.coord j (E.tIdx j)
def fam (i : ℕ) : PrimePattern d := fun j => E.coord j (E.famIdx i j)
def natoms (j : Fin d) : ℕ := (E.ld j).representatives.length
def tmask (j : Fin d) : ℕ := E.maskAt j (E.tIdx j)
def fmask (i : ℕ) (j : Fin d) : ℕ := E.maskAt j (E.famIdx i j)
/-- Target atoms of prime `j` outside the family's mask. -/
def badAt (i : ℕ) (j : Fin d) : ℕ := E.tmask j ^^^ (E.tmask j &&& E.fmask i j)

def isAtom (v : VarInfo d) (j : Fin d) (a : ℕ) : Bool :=
  match v with
  | .atom j' a' => j'.val == j.val && a' == a
  | _ => false

def gatePair : VarInfo d → VarInfo d → Bool
  | .gate j m, .atom j' a => j.val == j'.val && m.testBit a
  | _, _ => false

/-- At-least-one clause of prime `j`: every target atom has its positive literal. -/
def aloOK (j : Fin d) (c : RUP.Clause) : Bool :=
  (List.range (E.natoms j)).all fun a =>
    !(E.tmask j).testBit a || c.any fun l => l.2 && isAtom (E.vinfo l.1) j a

/-- Gate definition `g ∨ ¬v` with the atom `v` inside the gate's mask. -/
def gateOK (c : RUP.Clause) : Bool :=
  c.length == 2 && (c.getD 0 (0, false)).2 && !(c.getD 1 (0, false)).2 &&
    gatePair (E.vinfo (c.getD 0 (0, false)).1) (E.vinfo (c.getD 1 (0, false)).1)

/-- A negative literal true at every atom of `bad` at prime `j`. -/
def litCovers (j : Fin d) (bad : ℕ) (l : RUP.Literal) : Bool :=
  !l.2 && match E.vinfo l.1 with
    | .atom j' a => j'.val == j.val && !bad.testBit a
    | .gate j' m => j'.val == j.val && (m &&& bad) == 0
    | .unused => false

def famAt (i : ℕ) (c : RUP.Clause) (j : Fin d) : Bool :=
  decide (E.famIdx i j < (E.ld j).coordinates.length) &&
    (E.badAt i j == 0 || c.any (E.litCovers j (E.badAt i j)))

/-- Family clause: at every prime, the target atoms outside the family are excluded. -/
def famOK (i : ℕ) (c : RUP.Clause) : Bool :=
  decide (i < E.famCount) &&
    (List.range d).all fun jv => if h : jv < d then E.famAt i c ⟨jv, h⟩ else true

def originOK : Origin d → RUP.Clause → Bool
  | .alo j, c => E.aloOK j c
  | .gate, c => E.gateOK c
  | .fam i, c => E.famOK i c

end Env
end UC85
