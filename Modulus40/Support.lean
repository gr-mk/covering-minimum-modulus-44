import Modulus40.Basic

/-!
# Prime exponent supports

Ordinary moduli are products of powers of a fixed finite vector of distinct
primes. Fixed selectors give singleton exponent intervals, and arrow rays give
intervals without an upper bound. Disjoint boxes cannot repeat a modulus.
-/

namespace Modulus40

/-- The upper endpoint is inclusive; `none` means there is no upper bound. -/
structure SupportInterval where
  lo : ℕ
  hi : Option ℕ
  deriving DecidableEq, Repr

/-- A fixed exponent. -/
def SupportInterval.fixed (k : ℕ) : SupportInterval := ⟨k, some k⟩

/-- Every exponent at or above the given level. -/
def SupportInterval.ray (k : ℕ) : SupportInterval := ⟨k, none⟩

def SupportInterval.Contains (s : SupportInterval) (k : ℕ) : Prop :=
  s.lo ≤ k ∧ match s.hi with | none => True | some upper => k ≤ upper

instance (s : SupportInterval) (k : ℕ) : Decidable (s.Contains k) := by
  unfold SupportInterval.Contains
  cases s.hi <;> infer_instance

/-- The whole first interval lies strictly below the second one. -/
def SupportInterval.Before (s t : SupportInterval) : Prop :=
  match s.hi with | none => False | some upper => upper < t.lo

instance (s t : SupportInterval) : Decidable (s.Before t) := by
  unfold SupportInterval.Before
  cases s.hi <;> infer_instance

def SupportInterval.Separated (s t : SupportInterval) : Prop :=
  s.Before t ∨ t.Before s

instance (s t : SupportInterval) : Decidable (s.Separated t) :=
  inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem SupportInterval.contains_fixed (k n : ℕ) :
    (SupportInterval.fixed k).Contains n ↔ n = k := by
  simp [SupportInterval.fixed, SupportInterval.Contains]
  omega

@[simp] theorem SupportInterval.contains_ray (k n : ℕ) :
    (SupportInterval.ray k).Contains n ↔ k ≤ n := by
  simp [SupportInterval.ray, SupportInterval.Contains]

theorem SupportInterval.ne_of_before {s t : SupportInterval} {k l : ℕ}
    (h : s.Before t) (hk : s.Contains k) (hl : t.Contains l) : k ≠ l := by
  cases hs : s.hi with
  | none => simp [SupportInterval.Before, hs] at h
  | some upper =>
    have hku : k ≤ upper := by simpa [SupportInterval.Contains, hs] using hk.2
    have hul : upper < t.lo := by simpa [SupportInterval.Before, hs] using h
    have hll := hl.1
    omega

theorem SupportInterval.ne_of_separated {s t : SupportInterval} {k l : ℕ}
    (h : s.Separated t) (hk : s.Contains k) (hl : t.Contains l) : k ≠ l := by
  rcases h with h | h
  · exact SupportInterval.ne_of_before h hk hl
  · exact (SupportInterval.ne_of_before h hl hk).symm

abbrev ExponentVector (d : ℕ) := Fin d → ℕ
abbrev SupportBox (d : ℕ) := Fin d → SupportInterval

def SupportBox.Contains {d : ℕ} (box : SupportBox d) (e : ExponentVector d) : Prop :=
  ∀ i, (box i).Contains (e i)

instance {d : ℕ} (box : SupportBox d) (e : ExponentVector d) :
    Decidable (box.Contains e) :=
  inferInstanceAs (Decidable (∀ i, (box i).Contains (e i)))

def SupportBox.Separated {d : ℕ} (a b : SupportBox d) : Prop :=
  ∃ i, (a i).Separated (b i)

instance {d : ℕ} (a b : SupportBox d) : Decidable (a.Separated b) :=
  inferInstanceAs (Decidable (∃ i, (a i).Separated (b i)))

/-- The modulus represented by one exponent vector. -/
def supportModulus {d : ℕ} (primes : Fin d → ℕ) (e : ExponentVector d) : ℕ :=
  ∏ i, primes i ^ e i

/-- Unique factorization recovers every exponent from the represented modulus. -/
theorem supportModulus_factorization {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (e : ExponentVector d) (i : Fin d) :
    (supportModulus primes e).factorization (primes i) = e i := by
  unfold supportModulus
  rw [Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hprime j).ne_zero)]
  rw [Finset.sum_eq_single i]
  · rw [(hprime i).factorization_pow]
    simp
  · intro j _ hji
    rw [(hprime j).factorization_pow]
    apply Finsupp.single_eq_of_ne
    exact fun h => hji (hinj h.symm)
  · simp

/-- Distinct exponent vectors give distinct ordinary moduli. -/
theorem supportModulus_injective {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes) :
    Function.Injective (supportModulus primes) := by
  intro e f h
  funext i
  rw [← supportModulus_factorization primes hprime hinj e i,
    ← supportModulus_factorization primes hprime hinj f i, h]

theorem supportModulus_eq_iff {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (e f : ExponentVector d) :
    supportModulus primes e = supportModulus primes f ↔ e = f :=
  (supportModulus_injective primes hprime hinj).eq_iff

/-- A single separated coordinate certifies noncollision of entire boxes. -/
theorem SupportBox.modulus_ne_of_separated {d : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    {a b : SupportBox d} (hsep : a.Separated b)
    {e f : ExponentVector d} (he : a.Contains e) (hf : b.Contains f) :
    supportModulus primes e ≠ supportModulus primes f := by
  intro heq
  have hef := supportModulus_injective primes hprime hinj heq
  obtain ⟨i, hi⟩ := hsep
  exact SupportInterval.ne_of_separated hi (he i) (hf i) (congrFun hef i)

/-- The product of lower endpoints bounds every modulus in a box. -/
theorem SupportBox.modulus_lower_bound {d : ℕ} (primes : Fin d → ℕ)
    (hpos : ∀ i, 0 < primes i) (box : SupportBox d)
    {e : ExponentVector d} (he : box.Contains e) :
    supportModulus primes (fun i => (box i).lo) ≤ supportModulus primes e := by
  apply Finset.prod_le_prod'
  intro i _
  exact Nat.pow_le_pow_right (hpos i) (he i).1

/-- Every represented modulus is positive. -/
theorem supportModulus_pos {d : ℕ} (primes : Fin d → ℕ)
    (hpos : ∀ i, 0 < primes i) (e : ExponentVector d) :
    0 < supportModulus primes e := by
  exact Finset.prod_pos fun i _ => pow_pos (hpos i) _

/-- Products of powers of marker-free bases are themselves marker-free. -/
theorem supportModulus_not_dvd {d P : ℕ} (hP : P.Prime)
    (primes : Fin d → ℕ) (hfresh : ∀ i, ¬ P ∣ primes i) (e : ExponentVector d) :
    ¬ P ∣ supportModulus primes e := by
  apply Finset.prod_induction (fun i => primes i ^ e i) (fun n => ¬ P ∣ n)
  · intro a b ha hb h
    rcases hP.dvd_mul.mp h with h | h
    · exact ha h
    · exact hb h
  · exact hP.not_dvd_one
  · intro i _ h
    exact hfresh i (hP.dvd_of_dvd_pow h)

/-- If boxes are pairwise separated, the modulus identifies both the box and
its exponent vector. -/
theorem supported_modulus_eq_iff {d k : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (boxes : Fin k → SupportBox d)
    (hsep : ∀ i j, i ≠ j → (boxes i).Separated (boxes j))
    {i j : Fin k} {e f : ExponentVector d}
    (he : (boxes i).Contains e) (hf : (boxes j).Contains f) :
    supportModulus primes e = supportModulus primes f ↔ i = j ∧ e = f := by
  constructor
  · intro h
    refine ⟨?_, supportModulus_injective primes hprime hinj h⟩
    by_contra hij
    exact SupportBox.modulus_ne_of_separated primes hprime hinj (hsep i j hij) he hf h
  · rintro ⟨_, rfl⟩
    rfl

/-- A duplicate-free enumeration of supported exponent vectors produces
pairwise distinct moduli, both within each box and across boxes. -/
theorem supportedModuli_nodup {d k : ℕ} (primes : Fin d → ℕ)
    (hprime : ∀ i, (primes i).Prime) (hinj : Function.Injective primes)
    (boxes : Fin k → SupportBox d)
    (hsep : ∀ i j, i ≠ j → (boxes i).Separated (boxes j))
    (entries : List (Fin k × ExponentVector d))
    (hentries : entries.Nodup)
    (hsupport : ∀ entry ∈ entries, (boxes entry.1).Contains entry.2) :
    (entries.map fun entry => supportModulus primes entry.2).Nodup := by
  apply List.Nodup.map_on _ hentries
  intro x hx y hy h
  have hxy := (supported_modulus_eq_iff primes hprime hinj boxes hsep
    (hsupport x hx) (hsupport y hy)).mp h
  exact Prod.ext hxy.1 hxy.2

end Modulus40
