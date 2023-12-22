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

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` at an element `x` of an `AddCommMonoid` `S` that has natural number powers and an `R`-action.

## To do

* `smeval_neg` and `smeval_int_cast` for `R` a ring and `S` an `AddCommGroup`.
* `smeval_comp`, etc. for `R` commutative, `S` an `R`-algebra.
* Change `R`-algebra `S` to power-associative, when power-associativity is implemented.
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

end Module

section Algebra

variable (R : Type*) [CommSemiring R] {p : R[X]} {S : Type*} [Semiring S] [Algebra R S]

variable (r : R) (x : S) (p q : R[X])

theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, smeval_add, ph, qh]
  | h_monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, smeval_monomial, mul_one,
    pow_succ', smul_mul_assoc]

theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, mul_add]
  | h_monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial]
    rw [one_mul, pow_add, pow_one, ← mul_smul_comm, smeval_monomial]

theorem smeval_C_mul : (C r * p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [mul_add, smeval_add, ph, qh, smul_add]
  | h_monomial n b =>
    simp only [C_mul_monomial, smeval_monomial, mul_smul]

theorem smeval_mul_X_pow : ∀(n : ℕ), (p * X^n).smeval x = p.smeval x * x^n
  | 0 => by
    simp only [pow_zero, mul_one]
  | n + 1 => by
    rw [pow_add, ← mul_assoc, pow_one, smeval_mul_X, smeval_mul_X_pow n, pow_add, mul_assoc,
      pow_one]

theorem smeval_X_pow_mul : ∀(n : ℕ), (X^n * p).smeval x = x^n * p.smeval x
  | 0 => by
    simp [pow_zero, one_mul]
  | n + 1 => by
    rw [add_comm, pow_add, mul_assoc, pow_one, smeval_X_mul, smeval_X_pow_mul n, pow_add, mul_assoc,
      pow_one]

theorem smeval_monomial_mul (r : R) (n : ℕ) :
    smeval x (monomial n r * p) = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
    rw [← @C_mul_X_pow_eq_monomial, mul_assoc, smeval_C_mul, smeval_X_pow_mul, smeval_add]
  | h_monomial n a =>
    rw [smeval_monomial, monomial_mul_monomial, smeval_monomial, pow_add, mul_smul, mul_smul_comm]

theorem smeval_mul : (p * q).smeval x  = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
  | h_monomial n a =>
    simp only [smeval_monomial, smeval_C_mul, smeval_mul_X_pow, smeval_monomial_mul, smul_mul_assoc]

end Algebra

section Comparisons

theorem eval₂_eq_smeval (R : Type*) [Semiring R] {S : Type*} [Semiring S] (f : R →+* S) (p : R[X])
    (x: S) : haveI : Module R S := RingHom.toModule f
    p.eval₂ f x = p.smeval x := by
  letI : Module R S := RingHom.toModule f
  rw [smeval_eq_sum, eval₂_eq_sum]
  exact rfl

theorem leval_eq_smeval {R : Type*} [Semiring R] (r : R) : leval r =
    {
      toFun := fun p => p.smeval r
      map_add' := fun p q => smeval_add R p q r
      map_smul' := by
        intro r p
        simp only [smeval_smul, smul_eq_mul, RingHom.id_apply]
    } := by
  aesop

theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : Polynomial.aeval x =
    {
      toFun := fun p => @smeval S _ _ x R _ _ p
      map_one' := by simp only [smeval_one, pow_zero, one_smul]
      map_mul' := by
        intro p q
        simp only
        exact smeval_mul R x p q
      map_zero' := by simp only [smeval_zero]
      map_add' := fun p q => smeval_add R p q x
      commutes' := by
        intro r
        simp only
        rw [← C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smeval_C, pow_zero]
    } := by
  ext
  simp

end Comparisons
