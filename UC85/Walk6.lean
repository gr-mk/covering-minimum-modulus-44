import UC85.Glue

/-!
# Box-tree walks with a 6-bit prime field (up to 64 primes)

`walk6` is `UC85.walk` with node codes `2*(c + 64*(t + 256*(l + 2^21*r)))`, for systems with more than
32 primes; the fuel is a parameter.  New file: the built `Glue.lean` is untouched.
-/

namespace UC85
open Modulus40

def walk6 {d : ℕ} (info : ℕ → ℕ) (box : ℕ → SupportBox d) (i : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, n =>
    if info n % 2 = 1 then info n / 2 == i
    else if h : info n / 2 % 64 < d then
      if goesLeft (box i ⟨info n / 2 % 64, h⟩) (info n / 128 % 256) then
        walk6 info box i f (info n / 32768 % 2097152)
      else if goesRight (box i ⟨info n / 2 % 64, h⟩) (info n / 128 % 256) then
        walk6 info box i f (info n / 68719476736)
      else false
    else false

theorem walk6_sep {d : ℕ} {info : ℕ → ℕ} {box : ℕ → SupportBox d} {i j : ℕ} (hij : i ≠ j) :
    ∀ f n, walk6 info box i f n = true → walk6 info box j f n = true →
      (box i).Separated (box j) := by
  intro f
  induction f with
  | zero => intro n h; simp [walk6] at h
  | succ f ih =>
    intro n hi hj
    simp only [walk6] at hi hj
    by_cases hleaf : info n % 2 = 1
    · rw [if_pos hleaf, beq_iff_eq] at hi hj
      exact absurd (hi.symm.trans hj) hij
    rw [if_neg hleaf] at hi hj
    by_cases hc : info n / 2 % 64 < d
    swap
    · rw [dif_neg hc] at hi; simp at hi
    rw [dif_pos hc] at hi hj
    by_cases hLi : goesLeft (box i ⟨_, hc⟩) (info n / 128 % 256) = true <;>
      by_cases hLj : goesLeft (box j ⟨_, hc⟩) (info n / 128 % 256) = true
    · rw [if_pos hLi] at hi; rw [if_pos hLj] at hj; exact ih _ hi hj
    · rw [if_neg hLj] at hj
      by_cases hRj : goesRight (box j ⟨_, hc⟩) (info n / 128 % 256) = true
      · exact ⟨_, sep_of_sides hLi hRj⟩
      · rw [if_neg hRj] at hj; simp at hj
    · rw [if_neg hLi] at hi
      by_cases hRi : goesRight (box i ⟨_, hc⟩) (info n / 128 % 256) = true
      · exact ⟨_, Or.symm (sep_of_sides hLj hRi)⟩
      · rw [if_neg hRi] at hi; simp at hi
    · rw [if_neg hLi] at hi; rw [if_neg hLj] at hj
      by_cases hRi : goesRight (box i ⟨_, hc⟩) (info n / 128 % 256) = true
      swap
      · rw [if_neg hRi] at hi; simp at hi
      by_cases hRj : goesRight (box j ⟨_, hc⟩) (info n / 128 % 256) = true
      swap
      · rw [if_neg hRj] at hj; simp at hj
      rw [if_pos hRi] at hi; rw [if_pos hRj] at hj
      exact ih _ hi hj

theorem sep_of_walks6 {d k : ℕ} (info : ℕ → ℕ) (box : ℕ → SupportBox d) (F root : ℕ)
    (hw : ∀ i < k, walk6 info box i F root = true) :
    ∀ i j : Fin k, i ≠ j → (box i).Separated (box j) := fun i j hij =>
  walk6_sep (fun h => hij (Fin.ext h)) F root (hw i i.isLt) (hw j j.isLt)

end UC85
