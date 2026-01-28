/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Main variable of a polynomial

This file defines the *main variable* of a multivariate polynomial.
The main variable is the largest variable index appearing in the polynomial,
with respect to the linear order on the variable type.

## Main declarations

* `MvPolynomial.mainVariable p` : the largest variable index appearing in `p`.
  If `p = 0`, its main variable is `⊥`.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

+ `p : MvPolynomial σ R`

-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommSemiring R] [LinearOrder σ] {p : MvPolynomial σ R}

section MainVariable

/-! ### `mainVariable` -/


/-- The main variable of a multivariate polynomial `p` is the largest variable index
appearing in `p`. If `p = 0`, its main variable is `⊥`. -/
def mainVariable (p : MvPolynomial σ R) : WithBot σ := p.support.sup (fun s ↦ s.support.max)

variable (p) in
theorem mainVariable_def : p.mainVariable = p.support.sup (fun s ↦ s.support.max) := rfl

@[simp] theorem mainVariable_zero : (0 : MvPolynomial σ R).mainVariable = ⊥ := rfl

theorem ne_zero_of_mainVariable_ne_bot : p.mainVariable ≠ ⊥ → p ≠ 0 :=
  mt fun h ↦ h ▸ mainVariable_zero

@[simp] theorem mainVariable_monomial {r : R} (s : σ →₀ ℕ) (hr : r ≠ 0) :
    (monomial s r : MvPolynomial σ R).mainVariable = s.support.max := by
  rw [← single_eq_monomial, mainVariable, support, Finsupp.support_single_ne_zero s hr,
    Finset.sup_singleton]

@[simp] theorem mainVariable_C (r : R) : (C r : MvPolynomial σ R).mainVariable = ⊥ := by
  by_cases h : r = 0
  · simp only [mainVariable, h, C_0, support_zero, Finset.sup_empty]
  rw [C_apply, mainVariable_monomial _ h, Finsupp.support_zero, Finset.max_empty]

@[simp] theorem mainVariable_X_pow [Nontrivial R] (i : σ) {k : ℕ} (hk : k ≠ 0) :
    ((X i : MvPolynomial σ R) ^ k).mainVariable = i := by
  rewrite [X_pow_eq_monomial, mainVariable_monomial _ one_ne_zero, Finsupp.single]
  simp only [hk, reduceIte, Finset.max_singleton]

@[simp] theorem mainVariable_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainVariable = i :=
  (pow_one (X i : MvPolynomial σ R)).symm ▸ mainVariable_X_pow i Nat.one_ne_zero

theorem mainVariable_eq_bot_iff_eq_C : p.mainVariable = ⊥ ↔ (∃ r : R, p = C r) := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ h.choose_spec ▸ mainVariable_C h.choose)
  simp only [mainVariable, Finset.sup_eq_bot_iff, mem_support_iff, ne_eq] at h
  have h (m : σ →₀ ℕ) (hs : m ∈ p.support) : m = 0 :=
    have hs : ¬p.coeff m = 0 := mem_support_iff.mp hs
    Finsupp.support_eq_empty.mp <| Finset.max_eq_bot.mp (h m hs)
  have h : p.support = ∅ ∨ p.support = {0} :=
    Finset.subset_singleton_iff.mp <| Finset.coe_subset_singleton.mp h
  use ∑ s ∈ p.support, p.coeff s
  nth_rewrite 1 [map_sum, as_sum p]
  apply Or.elim h <;> (intro h; exact h ▸ rfl)

theorem mainVariable_add_le (p q : MvPolynomial σ R) :
    (p + q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  rewrite [mainVariable, mainVariable, mainVariable, ← Finset.sup_union]
  apply Finset.sup_le
  intro _ smem
  apply Finset.le_sup (support_add smem)

theorem mainVariable_mul_le (p q : MvPolynomial σ R) :
    (p * q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  apply Finset.sup_le
  intro s smem
  by_contra hs
  have ⟨hs1, hs2⟩ : (∀ x, ¬p.coeff x = 0 → x.support.max < s.support.max) ∧
      (∀ x, ¬q.coeff x = 0 → x.support.max < s.support.max):= by
    simp only [not_le, max_lt_iff] at hs
    have : ⊥ < s.support.max := bot_lt_of_lt hs.1
    simpa [mainVariable, Finset.sup_lt_iff this, mem_support_iff, ne_eq] using hs
  simp only [mem_support_iff, coeff_mul, ne_eq] at smem
  rcases Finset.exists_ne_zero_of_sum_ne_zero smem with ⟨⟨t1, t2⟩, ht1, ht2⟩
  simp only [Finset.mem_antidiagonal, ne_eq] at ht1 ht2
  rcases ne_zero_and_ne_zero_of_mul ht2 with ⟨ht2, ht3⟩
  absurd max_lt (hs1 t1 ht2) (hs2 t2 ht3)
  rewrite [not_lt, ← ht1, ← Finset.max_union]
  exact Finset.max_mono Finsupp.support_add

theorem mainVariable_sum_le {α : Type*} (s : Finset α) (f : α → MvPolynomial σ R) :
    (∑ a ∈ s, f a).mainVariable ≤ s.sup (fun a ↦ (f a).mainVariable) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s has ih
  rewrite [Finset.sum_insert has, Finset.sup_insert]
  exact (mainVariable_add_le _ _).trans (sup_le_sup_left ih _)

theorem mainVariable_prod_le {α : Type*} (s : Finset α) (f : α → MvPolynomial σ R) :
    (∏ a ∈ s, f a).mainVariable ≤ s.sup (fun a ↦ (f a).mainVariable) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sup_empty, le_bot_iff]; apply mainVariable_C
  | insert a s has ih =>
    rewrite [Finset.prod_insert has, Finset.sup_insert]
    exact (mainVariable_mul_le _ _).trans (sup_le_sup_left ih _)

theorem degreeOf_eq_zero_of_mainVariable_lt {i : σ} :
    p.mainVariable < i → p.degreeOf i = 0 := fun h ↦ by
  rewrite [degreeOf_eq_sup, ← Nat.bot_eq_zero, Finset.sup_eq_bot_iff, Nat.bot_eq_zero]
  intro s hs
  refine Finsupp.notMem_support_iff.mp ?_
  contrapose! h
  apply le_trans (Finset.le_max h)
  apply mainVariable_def p ▸ Finset.le_sup hs

theorem degreeOf_of_mainVariable_eq_bot (i : σ) : p.mainVariable = ⊥ → p.degreeOf i = 0 :=
  fun h ↦ degreeOf_eq_zero_of_mainVariable_lt (h ▸ WithBot.bot_lt_coe i)

end MainVariable

end MvPolynomial
