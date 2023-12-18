/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Polynomial.Induction
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval

/-!
# Scalar-multiple polynomial evaluation

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  This
is a generalization of `Data.Polynomial.Eval`.

## Main definitions

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` at an element in a power-associative `R`-algebra.

## To do

* `smeval_neg` and `smeval_int_cast` for `R` a ring and `S` an `AddCommGroup`.
* `smeval_mul`, `smeval_comp`, etc. for `R` commutative, `S` a power-associative `R`-algebra.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+`

-/

namespace Polynomial

section

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

@[simp]
theorem smeval_add (R : Type*) [Semiring R] [Module R S] (p q : R[X]) :
    (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) ?_ ?_
  intro i
  rw [smul_pow, zero_smul]
  intro i r s
  rw [smul_pow, smul_pow, smul_pow, add_smul]

theorem smeval_nat_cast (R : Type*) [Semiring R] [Module R S] (n : ℕ) :
    (n : R[X]).smeval x = n • x ^ 0 := by
  induction' n with n ih
  · simp only [smeval_zero, Nat.cast_zero, Nat.zero_eq, zero_smul]
  · rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

end

theorem smeval_eq_eval₂ (R : Type*) [Semiring R] {S : Type*} [Semiring S] (f : R →+* S) (p : R[X])
    (x: S) : haveI : Module R S := RingHom.toModule f
    p.smeval x = p.eval₂ f x := by
  letI : Module R S := RingHom.toModule f
  rw [smeval_eq_sum, eval₂_eq_sum]
  exact rfl
