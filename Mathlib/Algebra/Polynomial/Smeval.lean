/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Induction
import Mathlib.Algebra.Polynomial.Eval

/-!
# Scalar-multiple polynomial evaluation

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  This
is a generalization of `Algebra.Polynomial.Eval`.

## Main definitions

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `Semiring`
`R` at an element `x` of an `AddCommMonoid` `S` that has natural number powers and an `R`-action.
* `smeval.linearMap`: the `smeval` function as an `R`-linear map, when `S` is an `R`-module.
* `smeval.algebraMap`: the `smeval` function as an `R`-algebra map, when `S` is an `R`-algebra.

## Main results

* `smeval_monomial`: monomials evaluate as we expect.
* `smeval_add`, `smeval_smul`: linearity of evaluation, given an `R`-module.
* `smeval_mul`, `smeval_comp`: multiplicativity of evaluation, given power-associativity.
* `eval₂_eq_smeval`, `leval_eq_smeval.linearMap`, `aeval = smeval.algebraMap`, etc.: comparisons

## To do

* `smeval_neg` and `smeval_intCast` for `R` a ring and `S` an `AddCommGroup`.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+` (different file?)

-/

namespace Polynomial

section MulActionWithZero

variable {R : Type*} [Semiring R] (r : R) (p : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ]
  [MulActionWithZero R S] (x : S)

/-- Scalar multiplication together with taking a natural number power. -/
def smul_pow : ℕ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar semiring `R` at an element `x` in the target `S` using
scalar multiple `R`-action. -/
irreducible_def smeval : S := p.sum (smul_pow x)

theorem smeval_eq_sum : p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

@[simp]
theorem smeval_C : (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]
theorem smeval_monomial (n : ℕ) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

theorem eval_eq_smeval : p.eval r = p.smeval r := by
  rw [eval_eq_sum, smeval_eq_sum]
  rfl

theorem eval₂_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] (f : R →+* S) (p : R[X])
    (x: S) : letI : Module R S := RingHom.toModule f
    p.eval₂ f x = p.smeval x := by
  letI : Module R S := RingHom.toModule f
  rw [smeval_eq_sum, eval₂_eq_sum]
  rfl

variable (R)

@[simp]
theorem smeval_zero : (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, smul_pow, sum_zero_index]

@[simp]
theorem smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1, smeval_C]
  simp only [Nat.cast_one, one_smul]

@[simp]
theorem smeval_X :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

@[simp]
theorem smeval_X_pow {n : ℕ} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

end MulActionWithZero

section Module

variable (R : Type*) [Semiring R] (p q : R[X]) {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
  (x : S)

@[simp]
theorem smeval_add : (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) (fun _ ↦ ?_) (fun _ _ _ ↦ ?_)
  · rw [smul_pow, zero_smul]
  · rw [smul_pow, smul_pow, smul_pow, add_smul]

theorem smeval_natCast (n : ℕ) : (n : R[X]).smeval x = n • x ^ 0 := by
  induction' n with n ih
  · simp only [smeval_zero, Nat.cast_zero, Nat.zero_eq, zero_smul]
  · rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[deprecated (since := "2024-04-17")]
alias smeval_nat_cast := smeval_natCast

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
theorem smeval.linearMap_apply : smeval.linearMap R x p = p.smeval x := rfl

theorem leval_coe_eq_smeval {R : Type*} [Semiring R] (r : R) :
    ⇑(leval r) = fun p => p.smeval r := by
  rw [Function.funext_iff]
  intro
  rw [leval_apply, smeval_def, eval_eq_sum]
  rfl

theorem leval_eq_smeval.linearMap {R : Type*} [Semiring R] (r : R) :
    leval r = smeval.linearMap R r := by
  refine LinearMap.ext ?_
  intro
  rw [leval_apply, smeval.linearMap_apply, eval_eq_smeval]

end Module

section Neg

variable (R : Type*) [Ring R] {S : Type*} [AddCommGroup S] [Pow S ℕ] [Module R S] (p q : R[X])
  (x : S)

@[simp]
theorem smeval_neg : (-p).smeval x = - p.smeval x := by
  have h : (p + -p).smeval x = 0 := by rw [add_neg_self, smeval_zero]
  rw [smeval_add, add_eq_zero_iff_neg_eq] at h
  exact id h.symm

@[simp]
theorem smeval_sub : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg, smeval_add, smeval_neg, sub_eq_add_neg]

end Neg

section NatPowAssoc

/-!
In the module docstring for algebras at `Mathlib.Algebra.Algebra.Basic`, we see that
`[CommSemiring R] [Semiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]` is an
equivalent way to express `[CommSemiring R] [Semiring S] [Algebra R S]` that allows one to relax
the defining structures independently.  For non-associative power-associative algebras (e.g.,
octonions), we replace the `[Semiring S]` with `[NonAssocSemiring S] [Pow S ℕ] [NatPowAssoc S]`.
-/

variable (R : Type*) [Semiring R] {p : R[X]} (r : R) (p q : R[X]) {S : Type*}
  [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S] [Pow S ℕ]
  [NatPowAssoc S] (x : S)

theorem smeval_at_natCast (q : ℕ[X]): ∀(n : ℕ), q.smeval (n : S) = q.smeval n := by
  induction q using Polynomial.induction_on' with
  | h_add p q ph qh =>
    intro n
    simp only [add_mul, smeval_add, ph, qh, Nat.cast_add]
  | h_monomial n a =>
    intro n
    rw [smeval_monomial, smeval_monomial, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_npow]

@[deprecated (since := "2024-04-17")]
alias smeval_at_nat_cast := smeval_at_natCast

theorem smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S)  := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp_all only [smeval_add, coeff_add, add_smul]
  | h_monomial n a =>
    cases n with
    | zero => simp only [Nat.zero_eq, monomial_zero_left, smeval_C, npow_zero, coeff_C_zero]
    | succ n => rw [coeff_monomial_succ, smeval_monomial, npow_add, npow_one, mul_zero, zero_smul,
        smul_zero]

theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, smeval_add, ph, qh]
  | h_monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one, pow_succ',
      mul_assoc, npow_add, smul_mul_assoc, npow_one]

theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, mul_add]
  | h_monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, one_mul, npow_add,
      npow_one, ← mul_smul_comm, smeval_monomial]

theorem smeval_assoc_X_pow (m n : ℕ) :
    p.smeval x * x ^ m * x ^ n = p.smeval x * (x ^ m * x ^ n) := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, add_mul]
  | h_monomial n a =>
    rw [smeval_monomial, smul_mul_assoc, smul_mul_assoc, npow_mul_assoc, ← smul_mul_assoc]

theorem smeval_mul_X_pow : ∀ (n : ℕ), (p * X^n).smeval x = p.smeval x * x^n
  | 0 => by
    simp only [npow_zero, mul_one]
  | n + 1 => by
    rw [npow_add, ← mul_assoc, npow_one, smeval_mul_X, smeval_mul_X_pow n, npow_add,
      ← smeval_assoc_X_pow, npow_one]

theorem smeval_X_pow_assoc (m n : ℕ) :
    x ^ m * x ^ n * p.smeval x = x ^ m * (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, mul_add]
  | h_monomial n a =>
    simp only [smeval_monomial, mul_smul_comm, npow_mul_assoc]

theorem smeval_X_pow_mul : ∀ (n : ℕ), (X^n * p).smeval x = x^n * p.smeval x
  | 0 => by
    simp [npow_zero, one_mul]
  | n + 1 => by
    rw [add_comm, npow_add, mul_assoc, npow_one, smeval_X_mul, smeval_X_pow_mul n, npow_add,
      smeval_X_pow_assoc, npow_one]

theorem smeval_C_mul : (C r * p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [mul_add, smeval_add, ph, qh, smul_add]
  | h_monomial n b =>
    simp only [C_mul_monomial, smeval_monomial, mul_smul]

theorem smeval_monomial_mul (n : ℕ) :
    (monomial n r * p).smeval x = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, smeval_C_mul, smeval_X_pow_mul, smeval_add]
  | h_monomial n a =>
    rw [smeval_monomial, monomial_mul_monomial, smeval_monomial, npow_add, mul_smul, mul_smul_comm]

theorem smeval_mul : (p * q).smeval x  = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
  | h_monomial n a =>
    simp only [smeval_monomial, smeval_C_mul, smeval_mul_X_pow, smeval_monomial_mul, smul_mul_assoc]

theorem smeval_pow : ∀ (n : ℕ), (p^n).smeval x = (p.smeval x)^n
  | 0 => by
    simp only [npow_zero, smeval_one, one_smul]
  | n + 1 => by
    rw [npow_add, smeval_mul, smeval_pow n, pow_one, npow_add, npow_one]

theorem smeval_comp : (p.comp q).smeval x  = p.smeval (q.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp [add_comp, hr, hs, smeval_add]
  | h_monomial n a =>
    simp [smeval_monomial, smeval_C_mul, smeval_pow]

end NatPowAssoc

section Algebra

theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) (p : R[X]) : aeval x p = p.smeval x := by
  rw [aeval_def, eval₂_def, Algebra.algebraMap_eq_smul_one', smeval_def]
  simp only [Algebra.smul_mul_assoc, one_mul]
  exact rfl

theorem aeval_coe_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : ⇑(aeval x) = fun (p : R[X]) => p.smeval x := funext fun p => aeval_eq_smeval x p

end Algebra
