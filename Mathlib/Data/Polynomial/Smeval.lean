/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Induction
import Mathlib.Data.Polynomial.Eval

/-!
# Scalar-multiple polynomial evaluation over commutative semirings
This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a semiring `R`, and we evaluate at a weak form of `R`-algebra, namely an additive
commutative monoid with an action of `R` and a notion of natural number power.  We will later prove
stronger results for power-associative `R`-algebras.  This is a generalization of
`Data.Polynomial.Eval`.

## Main definitions
* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` at an element in a power-associative `R`-algebra.
* `smeval.algebraMap` def and `aeval = smeval.algebraMap` theorem.
* Nonunital evaluation for polynomials with vanishing constant term for `Pow S ℕ+` (different file?)

-/

namespace Polynomial

section MulActionWithZero

variable {S : Type*} [AddCommMonoid S] [Pow S ℕ] (x : S)

/-- Scalar multiplication by a natural number power. -/
def smul_pow {R : Type*} [Semiring R] [MulActionWithZero R S] : ℕ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar semiring `R` at an element `x` in the target `S` using
scalar multiple `R`-action. -/
irreducible_def smeval {R : Type*} [Semiring R] [MulActionWithZero R S] (p : R[X]) : S :=
  p.sum (smul_pow x)

theorem smeval_eq_sum {R : Type*} [Semiring R] [MulActionWithZero R S] (p : R[X]) :
    p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

@[simp]
theorem smeval_zero (R : Type*) [Semiring R] [MulActionWithZero R S] :
    (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, smul_pow, sum_zero_index]

theorem smeval_C {R : Type*} [Semiring R] [MulActionWithZero R S] (r : R) :
    (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

@[simp]
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
  induction n with
  | zero => rw [zero_nsmul, Nat.cast_zero, smeval_zero]
  | succ n ih => rw [n.cast_succ, smeval_add, ih, smeval_one, ← add_nsmul]

@[simp]
theorem smeval_smul (r : R) : (r • p).smeval x = r • p.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    rw [smul_add, smeval_add, ph, qh, ← smul_add, smeval_add]
  | h_monomial n a =>
    rw [smul_monomial, smeval_monomial, smeval_monomial, smul_assoc]

end Module

section NatPowAssoc

variable (R : Type*) [CommSemiring R] {p : R[X]} {S : Type*} (r : R)

variable [NonAssocSemiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]

variable [Pow S ℕ] [NatPowAssoc S]

variable (x : S) (p q : R[X])

theorem smeval_at_nat_cast (q : ℕ[X]): ∀(n : ℕ), q.smeval (n : S) = q.smeval n := by
  induction q using Polynomial.induction_on' with
  | h_add p q ph qh =>
    intro n
    simp only [add_mul, smeval_add, ph, qh, Nat.cast_add]
  | h_monomial n a =>
    intro n
    rw [smeval_monomial, smeval_monomial, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_npow]

--theorem smeval_at_zero : p.smeval (0 : S) = (p.coeff 0) • (1 : S)  := by
--  simp only [smeval_eq_sum, smul_pow]
  --simp_rw [zero_pow_eq, mul_ite, zero_pow]
  --simp (config := { contextual := true }) only [mul_zero, mul_one, sum, Classical.not_not,
  --mem_support_iff, sum_ite_eq', ite_eq_left_iff, imp_true_iff, eq_self_iff_true]

theorem smeval_mul_X : (p * X).smeval x = p.smeval x * x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [add_mul, smeval_add, ph, qh]
  | h_monomial n a =>
    simp only [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial, mul_one, pow_succ',
      mul_assoc]
    rw [npow_add, smul_mul_assoc, npow_one]

theorem smeval_X_mul : (X * p).smeval x = x * p.smeval x := by
    induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, mul_add]
  | h_monomial n a =>
    rw [← monomial_one_one_eq_X, monomial_mul_monomial, smeval_monomial]
    rw [one_mul, npow_add, npow_one, ← mul_smul_comm, smeval_monomial]

theorem smeval_assoc_X_pow (m n : ℕ) :
    p.smeval x * x ^ m * x ^ n = p.smeval x * (x ^ m * x ^ n) := by
  induction p using Polynomial.induction_on' with
  | h_add p q ph qh =>
    simp only [smeval_add, ph, qh, add_mul]
  | h_monomial n a =>
    rw [smeval_monomial, smul_mul_assoc, smul_mul_assoc, npow_mul_assoc, ← smul_mul_assoc]

theorem smeval_mul_X_pow : ∀(n : ℕ), (p * X^n).smeval x = p.smeval x * x^n
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

theorem smeval_X_pow_mul : ∀(n : ℕ), (X^n * p).smeval x = x^n * p.smeval x
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

theorem smeval_monomial_mul (r : R) (n : ℕ) :
    smeval x (monomial n r * p) = r • (x ^ n * p.smeval x) := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
    rw [← @C_mul_X_pow_eq_monomial, mul_assoc, smeval_C_mul, smeval_X_pow_mul, smeval_add]
  | h_monomial n a =>
    rw [smeval_monomial, monomial_mul_monomial, smeval_monomial, npow_add, mul_smul, mul_smul_comm]

theorem smeval_mul : (p * q).smeval x  = p.smeval x * q.smeval x := by
  induction p using Polynomial.induction_on' with
  | h_add r s hr hs =>
    simp only [add_comp, hr, hs, smeval_add, add_mul]
  | h_monomial n a =>
    simp only [smeval_monomial, smeval_C_mul, smeval_mul_X_pow, smeval_monomial_mul, smul_mul_assoc]

theorem smeval_pow : ∀(n : ℕ), (p^n).smeval x = (p.smeval x)^n
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

section Neg

--variable (R : Type*) [CommRing R] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]
--variable {S : Type v} [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S]

theorem _root_.Int.cast_neg_nat (G : Type*) [AddGroupWithOne G] (m : ℕ) : -(m : G) = (-m : ℤ) := by
  rw [neg_eq_iff_add_eq_zero, Int.cast_neg, Int.cast_ofNat, add_right_neg]

theorem smeval_at_neg_nat (S : Type*) [NonAssocRing S]  [Pow S ℕ] [NatPowAssoc S] (q : ℕ[X])
    (n : ℕ) : q.smeval (-(n : S)) = q.smeval (-n : ℤ) := by
    rw [smeval_eq_sum, smeval_eq_sum]
    simp only [smul_pow, sum_def, Int.cast_sum, Int.cast_mul, Int.cast_npow]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Int.cast_neg_nat, nsmul_eq_mul, ← Int.cast_ofNat, ← Int.cast_npow, ← Int.cast_mul,
      ← nsmul_eq_mul]

theorem smeval_neg (R : Type*) {S : Type*} [NonAssocRing S] [Pow S ℕ] [Ring R]
    [Module R S] (x : S) (p : R[X]) : (-p).smeval x = - p.smeval x := by
  have h : (p + -p).smeval x = 0 := by rw [add_neg_self, smeval_zero]
  rw [smeval_add, add_eq_zero_iff_neg_eq] at h
  exact id h.symm

theorem smeval_sub (R : Type*) {S : Type*} [NonAssocRing S] [Pow S ℕ] [CommRing R]
    [Module R S] (p q : R[X]) (x : S) : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg, smeval_add, smeval_neg, sub_eq_add_neg]

end Neg

section Comparison

theorem smeval_eq_eval {R : Type*} [Semiring R] (p : R[X]) (r : R) :
    p.smeval r = p.eval r := by
  rw [eval_eq_sum, smeval_eq_sum]
  exact rfl

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

/-- `Polynomial.smeval` as a linear map. -/
def smeval.linearMap {R : Type*} [Semiring R] {S : Type*} [AddCommMonoid S] [Pow S ℕ] [Module R S]
    (x : S) : R[X] →ₗ[R] S where
  toFun f := f.smeval x
  map_add' f g := by simp only [smeval_add]
  map_smul' c f := by simp only [smeval_smul, smul_eq_mul, RingHom.id_apply]

@[simp]
theorem smeval.linearMap_apply {R : Type*} [Semiring R] {S : Type*} [AddCommMonoid S] [Pow S ℕ]
    [Module R S] (x : S) (p : R[X]) : smeval.linearMap x p = smeval x p := rfl

theorem leval_eq_smeval {R : Type*} [Semiring R] (r : R) : leval r = smeval.linearMap r := by
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

/-- `Polynomial.smeval` as a linear map. -/
def smeval.algebraMap {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : R[X] →ₐ[R] S where
  toFun := fun p => @smeval S _ _ x R _ _ p
  map_one' := by simp only [smeval_one, pow_zero, one_smul]
  map_mul' := by
    intro p q
    simp only
    exact smeval_mul R x p q
  map_zero' := by simp only [smeval_zero]
  map_add' := fun p q => smeval_add x R p q
  commutes' := by
    intro r
    simp only
    rw [← C_eq_algebraMap, Algebra.algebraMap_eq_smul_one, smeval_C, pow_zero]

theorem smeval.algebraMap.apply {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) (p : R[X]) : smeval.algebraMap x p = smeval x p := rfl

theorem aeval_eq_smeval {R : Type*} [CommSemiring R] {S : Type*} [Semiring S] [Algebra R S]
    (x : S) : Polynomial.aeval x = @smeval.algebraMap R _ S _ _ x := by
  unfold aeval smeval.algebraMap
  ext
  simp only [eval₂AlgHom'_apply, eval₂_X, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, smeval_X, pow_one]

end Comparison

end Polynomial
