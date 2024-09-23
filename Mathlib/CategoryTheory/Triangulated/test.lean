import Mathlib

/- Calculs.-/

#eval 2 + 2

/- Exemples de termes.-/

/- Exemples d'énoncés.-/

/- Fonctions.-/

noncomputable def f : ℕ → ℝ := fun x ↦ √x

/- Produits.-/

#check ℕ × ℝ

noncomputable def a : ℕ × ℝ := ⟨0, Real.pi⟩

variable (x : ℕ × ℝ)

#check x.2

/- Sommes.-/

#check ℕ ⊕ ℝ

def a' : ℕ ⊕ ℝ := Sum.inr 0

/- Produit dépendant.-/

variable (ι : Type*) (α : ι → Type*)

#check (i : ι) → α i

def truc : (n : ℕ) → ℤ ⧸ Submodule.span ℤ {(n : ℤ)} := fun n ↦ 2^n


/- Somme dépendante.-/

#check Σ (i : ι), α i

example : Σ (n : ℕ), ℤ ⧸ Submodule.span ℤ {(n : ℤ)} := ⟨37, 0⟩

variable (t : Σ (i : ι), α i)

#check t.2

/- Types inductifs.-/

#print Nat


/- Propositions et preuves.-/

variable (P : Prop)

variable (p₁ p₂ : P)

example : p₁ = p₂ := Eq.refl _ --rfl

/- Implication.-/

variable (Q : Prop)

#check P → Q

variable (p : P) (I : P → Q)

example : Q := I p

example (n : ℕ) : n ≥ 1 → n ≠ 0 := by
  intro h
  by_contra h'
  rw [h'] at h
  linarith

/- Et.-/

variable (q : Q)

example : P ∧ Q := by --⟨p, q⟩
  constructor
  · exact p
  · exact q

/- Ou.-/

example : P ∨ Q := by
  left
  exact p

/- Quantificateur universel.-/

example : ∀ (x : ℝ), x ≠ 0 → x^2 ≠ 0 := by
  intro x hx
  have := pow_eq_zero_iff (M₀ := ℝ) (a := x) (n := 2)
  rw [ne_eq, this]
  exact hx
  linarith --exact two_ne_zero

/- Quantificateur existentiel.-/

example : ∃ (x : ℝ), x^2 = 3 := by
  use Real.sqrt 3
  have := Real.sq_sqrt (x := 3)
  apply this
  exact Nat.ofNat_nonneg 3

/- Preuve plus compliquée.-/

def truc_faux : Prop := ∀ (x : ℚ), x ≥ 0 → ∃ (y : ℚ), y^2 = x

example : ¬ truc_faux := by
  dsimp [truc_faux]
  push_neg
  use 3
  constructor
  · linarith
  · intro y
    by_contra habs
    have habs' := habs
    apply_fun (fun (a : ℚ) ↦ a * y.den^2) at habs
    rw [← mul_pow, Rat.mul_den_eq_num] at habs
    have habsZ : y.num ^ 2 = 3 * y.den ^ 2 := by
      rw [← Int.cast_inj (α := ℚ)]
      simp only [Int.cast_pow, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
      exact habs
    have habsN : y.num.natAbs ^ 2 = 3 * y.den ^ 2 := by
      rw [← Nat.cast_inj (R := ℤ)]
      simp only [Nat.cast_pow, Int.natCast_natAbs, sq_abs, Nat.cast_mul, Nat.cast_ofNat]
      exact habsZ
    have hdivnum : 3 ∈ y.num.natAbs.primeFactors := by
      rw [← Nat.primeFactors_pow (k := 2) _ (by simp only [ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true])]
      rw [Nat.primeFactors_eq_to_filter_divisors_prime]
      simp only [Finset.mem_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Int.natAbs_eq_zero, Rat.num_eq_zero]
      constructor
      · constructor
        · rw [habsN]
          simp only [dvd_mul_right]
        · by_contra hzero
          rw [hzero] at habs'
          linarith
      · exact Nat.prime_three
    have hdivden : 3 ∈ y.den.primeFactors := by
      have p3 : Nat.Prime 3 := Nat.prime_three
      suffices y.den.factorization 3 ≠ 0 by
      --  rw [← Function.mem_support] at this  -- ne marche pas car Lean va automatiquement
                                               -- transformer y.den.factorization en fonction
        rw [← Finsupp.mem_support_iff] at this
        rw [← Nat.support_factorization]
        exact this
      apply_fun (fun x ↦ x.factorization 3) at habsN
      simp [p3] at habsN
      by_contra h
      rw [h] at habsN
      simp only [mul_zero, add_zero, mul_eq_one, OfNat.ofNat_ne_one, false_and] at habsN
    have := Nat.Coprime.disjoint_primeFactors y.reduced
    rw [Finset.disjoint_left] at this
    exact this hdivnum hdivden

example : ¬ truc_faux := by
  dsimp [truc_faux]
  rw [Classical.not_forall]
  use 3
  rw [_root_.not_imp]
  constructor
  · linarith
  · by_contra h
    obtain ⟨y, hy⟩ := h
    apply_fun (fun x ↦ (x : ℝ)) at hy
    simp only [Rat.cast_pow, Rat.cast_ofNat] at hy
    have := irrational_nrt_of_notint_nrt 2 3 hy
    apply this
    · by_contra h
      obtain ⟨z, hz⟩ := h
      rw [hz] at hy
      have heq : z.natAbs^2 = 3 := by
        rw [← Nat.cast_inj (R := ℤ)]
        simp
        rw [← Int.cast_inj (α := ℝ)]
        simp
        exact hy
      by_cases h : z.natAbs ≤ 1
      · have := pow_le_one (a := z.natAbs) 2 (Nat.zero_le _) h
        rw [heq] at this
        linarith
      · rw [← lt_iff_not_le, ← Nat.succ_le_iff] at h
        have := pow_le_pow_left (a := 2) (by linarith) h 2
        rw [heq] at this
        linarith
    · linarith
    · simp only [Set.mem_range, Rat.cast_inj, exists_eq]
