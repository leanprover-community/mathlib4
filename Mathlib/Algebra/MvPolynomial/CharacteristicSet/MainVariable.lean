/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Variables

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
noncomputable def mainVariable (p : MvPolynomial σ R) : WithBot σ := p.vars.max

@[simp] theorem mainVariable_zero : (0 : MvPolynomial σ R).mainVariable = ⊥ := rfl

theorem ne_zero_of_mainVariable_ne_bot : p.mainVariable ≠ ⊥ → p ≠ 0 :=
  mt fun h ↦ h ▸ rfl

@[simp] theorem mainVariable_monomial {r : R} (s : σ →₀ ℕ) (h : r ≠ 0) :
    (monomial s r : MvPolynomial σ R).mainVariable = s.support.max := by
  rw [mainVariable, vars_monomial h]

@[simp] theorem mainVariable_C (r : R) : (C r : MvPolynomial σ R).mainVariable = ⊥ := by
  rw [mainVariable, vars_C, Finset.max_empty]

@[simp] theorem mainVariable_X_pow [Nontrivial R] (i : σ) {k : ℕ} (hk : k ≠ 0) :
    ((X i : MvPolynomial σ R) ^ k).mainVariable = i := by
  rewrite [X_pow_eq_monomial, mainVariable_monomial _ one_ne_zero, Finsupp.single]
  simp only [hk, reduceIte, Finset.max_singleton]

@[simp] theorem mainVariable_X [Nontrivial R] (i : σ) : (X i : MvPolynomial σ R).mainVariable = i :=
  (pow_one (X i : MvPolynomial σ R)).symm ▸ mainVariable_X_pow i Nat.one_ne_zero

theorem mainVariable_eq_bot_iff_degrees_eq_zero : p.mainVariable = ⊥ ↔ p.degrees = 0 := by
  rw [mainVariable, Finset.max_eq_bot, vars_def, Multiset.toFinset_eq_empty]

omit [LinearOrder σ] in
theorem degrees_eq_zero_iff_support_subset_zero : p.degrees = 0 ↔ p.support ⊆ {0} := by
  rewrite [Finset.subset_singleton_iff', Multiset.eq_zero_iff_forall_notMem]
  refine ⟨fun h s hs ↦ ?_, fun h i hi ↦ ?_⟩
  · apply Finsupp.support_eq_empty.mp
    refine Finset.eq_empty_of_forall_notMem fun i ↦ ?_
    have := (not_iff_not.mpr mem_degrees).mp (h i)
    have := not_and.mp <| not_exists.mp this s
    exact this (mem_support_iff.mp hs)
  rcases mem_degrees.mp hi with ⟨s, hs1, hs2⟩
  have := Finsupp.support_eq_empty.mpr (h s <| mem_support_iff.mpr hs1) ▸ hs2
  exact absurd this (Finset.notMem_empty i)

theorem mainVariable_eq_bot_iff_eq_C : p.mainVariable = ⊥ ↔ ∃ r : R, p = C r := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.choose_spec ▸ mainVariable_C h.choose⟩
  rw [mainVariable_eq_bot_iff_degrees_eq_zero] at h
  have h : p.support = ∅ ∨ p.support = {0} :=
    Finset.subset_singleton_iff.mp <| degrees_eq_zero_iff_support_subset_zero.mp h
  use ∑ s ∈ p.support, p.coeff s
  nth_rewrite 1 [map_sum, as_sum p]
  apply Or.elim h <;> (intro h; exact h ▸ rfl)

theorem mainVariable_add_le (p q : MvPolynomial σ R) :
    (p + q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  rewrite [mainVariable, mainVariable, mainVariable, ← Finset.max_union]
  exact Finset.max_mono <| vars_add_subset p q

theorem mainVariable_mul_le (p q : MvPolynomial σ R) :
    (p * q).mainVariable ≤ p.mainVariable ⊔ q.mainVariable := by
  rewrite [mainVariable, mainVariable, mainVariable, ← Finset.max_union]
  exact Finset.max_mono <| vars_mul p q

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

omit [LinearOrder σ] in
theorem support_subset_vars_of_mem_support {s : σ →₀ ℕ} (h : s ∈ p.support) :
    s.support ⊆ p.vars := fun i hi ↦ by
  contrapose! hi
  have := mem_support_notMem_vars_zero h hi
  exact Finsupp.notMem_support_iff.mpr this

theorem degreeOf_eq_zero_of_mainVariable_lt {i : σ} :
    p.mainVariable < i → p.degreeOf i = 0 := fun h ↦ by
  simp only [degreeOf, Multiset.count_eq_zero]
  intro hi
  have : i ∈ p.vars := by
    simpa only [vars, Multiset.mem_toFinset] using Multiset.mem_toFinset.mpr hi
  exact absurd h <| not_lt.mpr <| Finset.le_max this

theorem degreeOf_of_mainVariable_eq_bot (i : σ) : p.mainVariable = ⊥ → p.degreeOf i = 0 :=
  fun h ↦ degreeOf_eq_zero_of_mainVariable_lt (h ▸ WithBot.bot_lt_coe i)

end MainVariable

end MvPolynomial
