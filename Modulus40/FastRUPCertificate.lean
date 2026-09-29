import Modulus40.RUPCertificate
import Std.Data.TreeSet.Lemmas

/-! A balanced-tree implementation of the proved RUP checker. -/
namespace Modulus40
namespace FastRUP
open Std.Sat
open RUP (Literal Clause negate)

abbrev Known := Std.TreeSet Nat compare

def code (l : Literal) : Nat := 2 * l.1 + if l.2 then 1 else 0

theorem code_injective : Function.Injective code := by
  intro a b h
  rcases a with ⟨a, a'⟩
  rcases b with ⟨b, b'⟩
  cases a' <;> cases b' <;> simp_all [code] <;> omega

def reduce (known : Known) (clause : Clause) : Clause :=
  clause.filter fun l => !(known.contains (code (negate l)))

def propagate (known : Known) (hints : List Clause) : Bool :=
  List.rec (motive := fun _ => Known → Bool) (fun _ => false)
    (fun clause _ recur known =>
      match reduce known clause with
      | [] => true
      | [l] => recur (known.insert (code l))
      | _ => false) hints known

def knownOf (ls : List Literal) : Known :=
  ls.foldr (fun l known => known.insert (code l)) ∅

def check (clause : Clause) (hints : List Clause) : Bool :=
  propagate (knownOf (clause.map negate)) hints

def UnitsTrue (a : Nat → Bool) (known : Known) : Prop :=
  ∀ l, code l ∈ known → a l.1 = l.2

theorem unitsTrue_insert (a : Nat → Bool) (known : Known) (l : Literal)
    (hknown : UnitsTrue a known) (hl : a l.1 = l.2) :
    UnitsTrue a (known.insert (code l)) := by
  intro u hu
  rw [Std.TreeSet.mem_insert] at hu
  rcases hu with heq | hu
  · have heq : code l = code u := by simpa using heq
    have := code_injective heq
    simpa [← this] using hl
  · exact hknown u hu

theorem unitsTrue_knownOf (a : Nat → Bool) (ls : List Literal)
    (hls : ∀ l ∈ ls, a l.1 = l.2) : UnitsTrue a (knownOf ls) := by
  induction ls with
  | nil => intro l hl; simpa [knownOf] using hl
  | cons l ls ih =>
    apply unitsTrue_insert
    · exact ih (fun u hu => hls u (List.mem_cons_of_mem _ hu))
    · exact hls l (by simp)

theorem reduce_eval (a : Nat → Bool) (known : Known) (clause : Clause)
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
    have h := hknown (negate l) (Std.TreeSet.contains_iff_mem.mp hn)
    simp only [negate] at h
    rw [ha] at h
    cases l.2 <;> simp at h

theorem propagate_sound (a : Nat → Bool) (known : Known) (hints : List Clause)
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

theorem check_sound (a : Nat → Bool) (clause : Clause) (hints : List Clause)
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

def StepValid (clauses : Nat → Clause) (hints : Nat → List Nat) (i : Nat) : Prop :=
  (∀ j ∈ hints i, j < i) ∧ check (clauses i) ((hints i).map clauses) = true

instance (clauses : Nat → Clause) (hints : Nat → List Nat) (i : Nat) :
    Decidable (StepValid clauses hints i) := inferInstanceAs (Decidable (_ ∧ _))

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

end FastRUP
end Modulus40
