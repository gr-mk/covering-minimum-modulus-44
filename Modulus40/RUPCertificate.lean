import Mathlib.Data.List.Basic
import Std.Sat.CNF

/-!
# Kernel-reducible reverse-unit-propagation certificates

Each derived clause is checked using only its explicitly listed earlier hints.
No hash tables, native evaluator, or external solver is part of the trusted proof.
-/

namespace Modulus40
namespace RUP
open Std.Sat

abbrev Literal := Nat × Bool
abbrev Clause := CNF.Clause Nat

def negate (l : Literal) : Literal := (l.1, !l.2)

/-- Remove literals contradicted by the currently known unit literals. -/
def reduce (known : List Literal) (clause : Clause) : Clause :=
  clause.filter fun l => !(known.contains (negate l))

/-- Follow an ordered list of unit-propagation hints. -/
def propagate : List Literal → List Clause → Bool
  | _, [] => false
  | known, clause :: hints =>
    match reduce known clause with
    | [] => true
    | [l] => propagate (l :: known) hints
    | _ => false

/-- Check that falsifying `clause` makes its hints contradictory. -/
def check (clause : Clause) (hints : List Clause) : Bool :=
  propagate (clause.map negate) hints

def UnitsTrue (a : Nat → Bool) (known : List Literal) : Prop :=
  ∀ l ∈ known, a l.1 = l.2

theorem reduce_eval (a : Nat → Bool) (known : List Literal) (clause : Clause)
    (hknown : UnitsTrue a known) :
    (reduce known clause).eval a = clause.eval a := by
  apply Bool.eq_iff_iff.mpr
  simp only [reduce, CNF.Clause.eval, List.any_eq_true, List.mem_filter,
    Bool.not_eq_true', beq_iff_eq]
  constructor
  · rintro ⟨l, ⟨hl, _⟩, ha⟩
    exact ⟨l, hl, ha⟩
  · rintro ⟨l, hl, ha⟩
    refine ⟨l, ⟨hl, ?_⟩, ha⟩
    apply Bool.eq_false_iff.mpr
    intro hn
    have h := hknown (negate l) (by simpa using hn)
    simp only [negate] at h
    rw [ha] at h
    cases l.2 <;> simp at h

theorem propagate_sound (a : Nat → Bool) (known : List Literal) (hints : List Clause)
    (hknown : UnitsTrue a known) (hhints : ∀ c ∈ hints, c.eval a = true) :
    propagate known hints = false := by
  induction hints generalizing known with
  | nil => rfl
  | cons c rest ih =>
    have hc := hhints c (by simp)
    have hr := reduce_eval a known c hknown
    unfold propagate
    split
    next heq => simp [heq] at hr; simp [hr] at hc
    next l heq =>
      apply ih
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · simpa [heq, CNF.Clause.eval] using hr.trans hc
        · exact hknown u hu
      · intro c hc
        exact hhints c (List.mem_cons_of_mem _ hc)
    next => rfl

theorem check_sound (a : Nat → Bool) (clause : Clause) (hints : List Clause)
    (hcheck : check clause hints = true) (hhints : ∀ c ∈ hints, c.eval a = true) :
    clause.eval a = true := by
  cases heval : clause.eval a with
  | true => rfl
  | false =>
    have hknown : UnitsTrue a (clause.map negate) := by
      intro l hl
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
      have hfalse : a u.1 != u.2 := by
        have h := List.any_eq_false.mp heval u hu
        simpa using h
      cases ha : a u.1 <;> cases hb : u.2 <;> simp_all [negate]
    have h := propagate_sound a _ hints hknown hhints
    simp only [check] at hcheck
    simp [h] at hcheck

/-- Local conditions for one derived clause in a topologically ordered proof. -/
def StepValid (clauses : Nat → Clause) (hints : Nat → List Nat) (i : Nat) : Prop :=
  (∀ j ∈ hints i, j < i) ∧ check (clauses i) ((hints i).map clauses) = true

instance (clauses : Nat → Clause) (hints : Nat → List Nat) (i : Nat) :
    Decidable (StepValid clauses hints i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Soundness of the entire DAG of reverse-unit-propagation steps. -/
theorem clauses_true (clauses : Nat → Clause) (hints : Nat → List Nat)
    (initial count : Nat) (hsteps : ∀ i, initial ≤ i → i < count → StepValid clauses hints i)
    (a : Nat → Bool) (hinitial : ∀ i < initial, (clauses i).eval a = true) :
    ∀ i < count, (clauses i).eval a = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hicount
    by_cases hi : i < initial
    · exact hinitial i hi
    · have hs := hsteps i (Nat.le_of_not_gt hi) hicount
      apply check_sound a (clauses i) ((hints i).map clauses) hs.2
      intro c hc
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
      have hji := hs.1 j hj
      exact ih j hji (Nat.lt_trans hji hicount)

/-- An empty final clause certifies unsatisfiability of the original formula. -/
theorem unsat_of_certificate (cnf : CNF Nat) (clauses : Nat → Clause)
    (hints : Nat → List Nat) (initial count final : Nat)
    (hinitial : ∀ i < initial, clauses i ∈ cnf)
    (hsteps : ∀ i, initial ≤ i → i < count → StepValid clauses hints i)
    (hfinal : final < count) (hempty : clauses final = []) : cnf.Unsat := by
  intro a
  apply Bool.eq_false_iff.mpr
  intro hsat
  have hc := clauses_true clauses hints initial count hsteps a
    (fun i hi => List.all_eq_true.mp hsat _ (hinitial i hi)) final hfinal
  simpa [hempty] using hc

end RUP
end Modulus40
