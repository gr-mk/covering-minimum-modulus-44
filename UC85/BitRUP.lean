import Modulus40.FastRUPCertificate

/-!
# A bitmask RUP checker (UC85 pilot)

Same certificate format and soundness statement as gr-mk's `FastRUP`, but the set of known
unit literals is a natural number used as a bit set (`Nat.testBit`, `|||`, `<<<`), which the
kernel evaluates with GMP arithmetic instead of balanced-tree operations.
-/

namespace UC85
namespace BitRUP
open Modulus40 Std.Sat
open Modulus40.RUP (Literal Clause negate)

def bit (l : Literal) : ℕ := 1 <<< FastRUP.code l

def reduce (known : ℕ) (clause : Clause) : Clause :=
  clause.filter fun l => !(known.testBit (FastRUP.code (negate l)))

def propagate (known : ℕ) (hints : List Clause) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => false)
    (fun clause _ recur known =>
      match reduce known clause with
      | [] => true
      | [l] => recur (known ||| bit l)
      | _ => false) hints known

def knownOf (ls : List Literal) : ℕ := ls.foldr (fun l known => known ||| bit l) 0

def check (clause : Clause) (hints : List Clause) : Bool :=
  propagate (knownOf (clause.map negate)) hints

def UnitsTrue (a : ℕ → Bool) (known : ℕ) : Prop :=
  ∀ l, known.testBit (FastRUP.code l) = true → a l.1 = l.2

theorem testBit_or_bit (known : ℕ) (l u : Literal) :
    (known ||| bit l).testBit (FastRUP.code u) = true ↔
      known.testBit (FastRUP.code u) = true ∨ u = l := by
  rw [Nat.testBit_or, bit, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact or_congr Iff.rfl ⟨fun h => FastRUP.code_injective h.symm, fun h => by rw [h]⟩

theorem unitsTrue_insert (a : ℕ → Bool) (known : ℕ) (l : Literal)
    (hknown : UnitsTrue a known) (hl : a l.1 = l.2) : UnitsTrue a (known ||| bit l) := by
  intro u hu
  rcases (testBit_or_bit known l u).1 hu with h | rfl
  · exact hknown u h
  · exact hl

theorem unitsTrue_knownOf (a : ℕ → Bool) (ls : List Literal)
    (hls : ∀ l ∈ ls, a l.1 = l.2) : UnitsTrue a (knownOf ls) := by
  induction ls with
  | nil => intro l hl; simp [knownOf] at hl
  | cons l ls ih =>
    apply unitsTrue_insert
    · exact ih (fun u hu => hls u (List.mem_cons_of_mem _ hu))
    · exact hls l (by simp)

theorem reduce_eval (a : ℕ → Bool) (known : ℕ) (clause : Clause)
    (hknown : UnitsTrue a known) : (reduce known clause).eval a = clause.eval a := by
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
    have h := hknown (negate l) hn
    simp only [negate] at h
    rw [ha] at h
    cases l.2 <;> simp at h

theorem propagate_sound (a : ℕ → Bool) (known : ℕ) (hints : List Clause)
    (hknown : UnitsTrue a known) (hhints : ∀ c ∈ hints, c.eval a = true) :
    propagate known hints = false := by
  induction hints generalizing known with
  | nil => rfl
  | cons c rest ih =>
    have hc := hhints c (by simp)
    have hr := reduce_eval a known c hknown
    unfold propagate
    dsimp only
    split
    next heq => simp [heq] at hr; simp [hr] at hc
    next l heq =>
      apply ih
      · apply unitsTrue_insert a known l hknown
        simpa [heq, CNF.Clause.eval] using hr.trans hc
      · intro c hc
        exact hhints c (List.mem_cons_of_mem _ hc)
    next => rfl

theorem check_sound (a : ℕ → Bool) (clause : Clause) (hints : List Clause)
    (hcheck : check clause hints = true) (hhints : ∀ c ∈ hints, c.eval a = true) :
    clause.eval a = true := by
  cases heval : clause.eval a with
  | true => rfl
  | false =>
    have hknown : UnitsTrue a (knownOf (clause.map negate)) := by
      apply unitsTrue_knownOf
      intro l hl
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
      have hfalse : a u.1 != u.2 := by
        have h := List.any_eq_false.mp heval u hu
        simpa using h
      cases ha : a u.1 <;> cases hb : u.2 <;> simp_all [negate]
    have h := propagate_sound a _ hints hknown hhints
    simp only [check] at hcheck
    simp [h] at hcheck

def StepValid (clauses : ℕ → Clause) (hints : ℕ → List ℕ) (i : ℕ) : Prop :=
  (∀ j ∈ hints i, j < i) ∧ check (clauses i) ((hints i).map clauses) = true

instance (clauses : ℕ → Clause) (hints : ℕ → List ℕ) (i : ℕ) :
    Decidable (StepValid clauses hints i) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every clause of a BitRUP-checked certificate holds under any assignment satisfying its
initial clauses (the analogue of `FastRUP.clauses_true`). -/
theorem clauses_true (clauses : ℕ → Clause) (hints : ℕ → List ℕ)
    (initial count : ℕ) (hsteps : ∀ i, initial ≤ i → i < count → StepValid clauses hints i)
    (a : ℕ → Bool) (hinitial : ∀ i < initial, (clauses i).eval a = true) :
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

end BitRUP
end UC85
