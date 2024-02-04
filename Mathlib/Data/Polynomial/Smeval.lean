/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Data.Polynomial.Induction
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Eval

/-!
# Scalar-multiple polynomial evaluation

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  This
is a generalization of `Data.Polynomial.Eval`.

## Main definitions

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `Semiring`
`R` at an element `x` of an `AddCommMonoid` `S` that has natural number powers and an `R`-action.

## To do

* `smeval_neg` and `smeval_int_cast` for `R` a ring and `S` an `AddCommGroup`.
* `smeval_mul`, `smeval_comp`, etc. for `R` commutative, `S` a power-associative non-assoc. `R`-alg.
* `smeval.algebraMap` def and `aeval = smeval.algebraMap` theorem.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+` (different file?)

-/

namespace Polynomial

section MulActionWithZero

variable {S : Type*} [AddCommMonoid S] [Pow S ℕ] (x : S)

/-- Scalar multiplication together with taking a natural number power. -/
def smul_pow {R : Type*} [Semiring R] [MulActionWithZero R S] : ℕ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar commutative semiring `R` at an element `x` in the target
`S` using scalar multiple `R`-action. -/
irreducible_def smeval {R : Type*} [Semiring R] [MulActionWithZero R S] (p : R[X]) : S :=
  p.sum (smul_pow x)

theorem smeval_eq_sum {R : Type*} [Semiring R] [MulActionWithZero R S] (p : R[X]) :
    p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

@[simp]
theorem smeval_zero (R : Type*) [Semiring R] [MulActionWithZero R S] :
    (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, smul_pow, sum_zero_index]

@[simp]
theorem smeval_C {R : Type*} [Semiring R] [MulActionWithZero R S] (r : R) :
    (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]
theorem smeval_one (R : Type*) [Semiring R] [MulActionWithZero R S] :
    (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1, smeval_C]
  simp only [Nat.cast_one, one_smul]

@[simp]
theorem smeval_X (R : Type*) [Semiring R] [MulActionWithZero R S] :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]
theorem smeval_monomial {R : Type*} [Semiring R] [MulActionWithZero R S] (r : R) (n : ℕ) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

@[simp]
theorem smeval_X_pow (R : Type*) [Semiring R] [MulActionWithZero R S] {n : ℕ} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

end MulActionWithZero

section Module

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

@[simp]
theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) ?_ ?_
  intro i
  rw [smul_pow, zero_smul]
  intro i r s
  rw [smul_pow, smul_pow, smul_pow, add_smul]

theorem smeval_nat_cast (n : ℕ) : (n : R[X]).smeval x = n • x ^ 0 := by
  induction' n with n ih
  · simp only [smeval_zero, Nat.cast_zero, Nat.zero_eq, zero_smul]
  · rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]
theorem smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | h_monomial n a =>
    rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

/-- `Polynomial.smeval` as a linear map. -/
def smeval.linearMap : R[X] →ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem smeval.linearMap_apply : smeval.linearMap R x p = smeval x p := rfl

end Module

section Comparisons

theorem eval₂_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] (f : R →+* S) (p : R[X])
    (x: S) : haveI : Module R S := RingHom.toModule f
    p.eval₂ f x = p.smeval x := by
  letI : Module R S := RingHom.toModule f
  rw [smeval_eq_sum, eval₂_eq_sum]
  exact rfl

theorem leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) :
    ⇑(leval r) = fun p => p.smeval r := by
  rw [@Function.funext_iff]
  intro
  rw [leval_apply, smeval_def, eval_eq_sum]
  exact rfl

theorem leval_eq_smeval {R : Type*} [Semiring R] (r : R) : leval r = smeval.linearMap R r := by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply, smeval.linearMap_apply, ← eval₂_eq_smeval R (RingHom.id _), eval]

theorem aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : ⇑(aeval x) = fun p => @smeval S _ _ x R _ _ p := by
  refine funext ?_
  intro
  rw [aeval_def, eval₂_def, Algebra.algebraMap_eq_smul_one', smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

end Comparisons
