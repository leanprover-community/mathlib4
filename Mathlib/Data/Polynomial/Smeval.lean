/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.PowAssoc
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Polynomial.Induction
import Mathlib.Data.Polynomial.Basic

/-!
# Scalar-multiple polynomial evaluation over commutative semirings

This file defines polynomial evaluation via scalar multiplication.  Our polynomials have
coefficients in a commutative semiring `R`, and we evaluate at a weak form of `R`-algebra, namely a
commutative monoid with a multiplicative action of `R` and a notion of power.  We will later prove
stronger results for power-associative `R`-algebras.  This is analogous to `Data.Polynomial.Eval`,
the difference being that the former is about `*`, while the present file is about `•`.

## Main definitions

* `Polynomial.smnueval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` and vanishing constant term at an element in a non-unital power-associative `R`-algebra.

* `Polynomial.smeval`: function for evaluating a polynomial with coefficients in a `CommSemiring`
`R` at an element in a power-associative `R`-algebra.

## Things I need

* I was hoping for `NonUnitalPowAssocMul` and `PowAssocMul` in Mathlib.Algebra.Group.Defs.  However,
the consensus is that we can just use `Prop`-valued mixin and write a `Pow` instance.

* Maybe put `NonUnitalPowAssocSemiring` and `PowAssocSemiring` in Mathlib.Algebra.Ring.Defs.
Once again, I guess we just use the mixin: `[NonUnitalPowAssocSemiring A] [Powassoc A]`

* I should make a ncpoly class, for polynomials with no constant.  Notation should be `XR[X]`.  For
now we use `Finsupp` ℕ+ →₀ R, so `p.support` is a `Finset ℕ+`, `p.sum` is a sum over that.  Maybe
write a function that restricts a polynomial to a ncpoly, and one that extends a ncpoly to poly.

-- A Non-unital non-associative `R`-algebra `A` is defined by the combination
`[NonUnitalNonAssocSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]`


## Tags

`CommSemiring`, ` Non-unital Power-associative algebra`
-/

universe u v w x

open Finset AddMonoidAlgebra

open BigOperators

namespace Polynomial

section NonUnital

variable {R : Type u} [Semiring R] {p : R[X]} {S : Type v}

variable [AddCommMonoid S] [MulActionWithZero R S] [Pow S ℕ+] (p: ℕ+ →₀ R) (x : S)

/-- Scalar multiplication by a positive power. -/
def smul_ppow : ℕ+ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar commutative semiring `R` with vanishing constant term at
an element `x` in the target object `S` with scalar multiplication by `R`. We allow any polynomial,
but get wrong answers when there are constant terms. -/
irreducible_def smnueval : S := p.sum (smul_ppow x)

theorem smnueval_eq_sum : smnueval p x = p.sum (smul_ppow x) := by
  rw [smnueval_def]

theorem smnueval_zero : smnueval (0 : ℕ+ →₀ R ) x = (0 : S) := by
  simp only [smnueval_eq_sum, Finsupp.sum_zero_index]

theorem smnueval_X : smnueval (Finsupp.single 1 1) x = x ^ (1 : ℕ+) := by
  simp only [smnueval_eq_sum, smul_ppow, zero_smul, Finsupp.sum_single_index, one_smul]

theorem smnueval_monomial (r : R) (n : ℕ+) : smnueval (Finsupp.single n r) x = r • x ^ n := by
  simp only [smnueval_eq_sum, smul_ppow, zero_smul, Finsupp.sum_single_index]

theorem smnueval_X_pow {n : ℕ+} : smnueval (Finsupp.single n (1 : R)) x = x ^ n := by
  rw [← one_smul R (x^n)]
  exact smnueval_monomial x 1 n

end NonUnital

section Unital

variable {S : Type v} [AddCommMonoid S] [Pow S ℕ] (x : S)

/-- Scalar multiplication by a natural number power. -/
def smul_pow {R : Type u} [Semiring R] [MulActionWithZero R S] : ℕ → R → S := fun n r => r • x^n

/-- Evaluate a polynomial `p` in the scalar commutative semiring `R` at an element `x` in the target
power-associative `R`-algebra `S`. -/
irreducible_def smeval {R : Type u} [Semiring R] [MulActionWithZero R S] (p : R[X]) : S :=
  p.sum (smul_pow x)

theorem smeval_eq_sum {R : Type u} [Semiring R] [MulActionWithZero R S] (p : R[X]) :
    p.smeval x = p.sum (smul_pow x) := by rw [smeval_def]

theorem smeval_zero (R : Type u) [Semiring R] [MulActionWithZero R S] :
    (0 : R[X]).smeval x = 0 := by
  simp only [smeval_eq_sum, smul_pow, sum_zero_index]

theorem smeval_C {R : Type u} [Semiring R] [MulActionWithZero R S] (r : R) :
    (C r).smeval x = r • x ^ 0 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_C_index]

theorem smeval_one (R : Type u) [Semiring R] [MulActionWithZero R S] :
    (1 : R[X]).smeval x = 1 • x ^ 0 := by
  rw [← C_1, smeval_C]
  simp only [Nat.cast_one, one_smul]

theorem smeval_X (R : Type u) [Semiring R] [MulActionWithZero R S] :
    (X : R[X]).smeval x = x ^ 1 := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_X_index, one_smul]

theorem smeval_monomial {R : Type u} [Semiring R] [MulActionWithZero R S] (r : R) (n : ℕ) :
    (monomial n r).smeval x = r • x ^ n := by
  simp only [smeval_eq_sum, smul_pow, zero_smul, sum_monomial_index]

theorem smeval_X_pow (R : Type u) [Semiring R] [MulActionWithZero R S] {n : ℕ} :
    (X ^ n : R[X]).smeval x = x ^ n := by
  simp only [smeval_eq_sum, smul_pow, X_pow_eq_monomial, zero_smul, sum_monomial_index, one_smul]

theorem smeval_eq_eval {R : Type u} [Semiring R] (p : R[X]) (r : R) :
    p.smeval r = p.eval r := by
  rw [eval_eq_sum, smeval_eq_sum]
  exact rfl

theorem smeval_nat_cast (R : Type u) [Semiring R] [Module R S] : ∀(n : ℕ),
    (n : R[X]).smeval x = n • x ^ 0
  | 0 => by
    rw [zero_nsmul, Nat.cast_zero, smeval_zero]
  | n + 1 => by
    rw [Nat.cast_succ, add_smul, ← smeval_nat_cast R n, ← smeval_one x R]
    simp only [smeval_eq_sum]
    refine sum_add_index (n : R[X]) (1 : R[X]) (smul_pow x) ?_ ?_
    intro i
    rw [smul_pow, zero_smul]
    intros
    simp only [smul_pow, add_smul]

theorem smeval_add (R : Type u) [Semiring R] [Module R S] (p q : R[X]) :
    (p + q).smeval x = p.smeval x + q.smeval x := by
  simp only [smeval_eq_sum, smul_pow]
  refine sum_add_index p q (smul_pow x) ?_ ?_
  intro i
  rw [smul_pow, zero_smul]
  intro i r s
  rw [smul_pow, smul_pow, smul_pow, add_smul]

/-!
@[simp, norm_cast]
theorem Nat.cast_npow [Semiring R] (n m : ℕ) : (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction' m with m ih
  · simp
  · rw [_root_.pow_succ', _root_.pow_succ', Nat.cast_mul, ih]

I want compare sums

-/

end Unital

section NonUnitalPowAssoc

variable {R : Type u} [Semiring R] {p : R[X]} {S : Type v}

variable [NonUnitalNonAssocSemiring S] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]

variable [Pow S ℕ+] [PNatPowAssoc S] (p: ℕ+ →₀ R) (x : S)

theorem _root_.zero_ppow (n : ℕ+) : (0:S)^n = 0 := by
  refine PNat.recOn n (ppow_one 0) ?_
  intro n _
  rw [ppow_add, ppow_one, mul_zero]

theorem smul_ppow_zero (n : ℕ+) (r : R) : smul_ppow (0 : S) n r = 0 := by
  refine PNat.recOn n ?_ ?_
  rw[smul_ppow, ppow_one, smul_zero]
  intro n _
  rw [smul_ppow, ppow_add, ppow_one, mul_zero, smul_zero]

theorem smnueval_at_zero : smnueval p (0:S) = 0 := by
  simp only [smnueval_eq_sum]
  rw[Finsupp.sum]
  simp_rw [smul_ppow_zero]
  simp only [sum_const_zero]

-- smnueval_mul_X, smnuevalcomp, etc.

end NonUnitalPowAssoc

section UnitalPowAssoc

variable (R : Type u) [CommSemiring R] {p : R[X]} {S : Type v} (r : R)

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
    rw [smeval_monomial, smul_mul_assoc, smul_mul_assoc, ← npow_assoc, ← smul_mul_assoc]

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
    simp only [smeval_monomial, mul_smul_comm, npow_assoc]

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

end UnitalPowAssoc

section test

--variable (R : Type u) [CommRing R] [Module R S] [IsScalarTower R S S] [SMulCommClass R S S]
--variable {S : Type v} [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S]

theorem _root_.Int.cast_neg_nat (G : Type v) [AddGroupWithOne G] (m : ℕ) : -(m : G) = (-m : ℤ) := by
  rw [neg_eq_iff_add_eq_zero, Int.cast_neg, Int.cast_ofNat, add_right_neg]

theorem smeval_at_neg_nat (S : Type v) [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] (q : ℕ[X])
    (n : ℕ) : q.smeval (-(n : S)) = q.smeval (-n : ℤ) := by
    rw [smeval_eq_sum, smeval_eq_sum]
    unfold smul_pow
    simp only [sum_def, Int.cast_sum, Int.cast_mul, Int.cast_npow]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [Int.cast_neg_nat, ← @smul_one_mul, nsmul_one]
    simp only [Int.cast_neg, Int.cast_ofNat, nsmul_eq_mul, Int.cast_mul, Int.cast_npow]

theorem smeval_neg (R : Type u) {S : Type v} [NonAssocRing S] [Pow S ℕ] [Ring R]
    [Module R S] (x : S) (p : R[X]) : (-p).smeval x = - p.smeval x := by
  have h : (p + -p).smeval x = 0 := by rw [add_neg_self, smeval_zero]
  rw [smeval_add, add_eq_zero_iff_neg_eq] at h
  exact id h.symm

theorem smeval_sub (R : Type u) {S : Type v} [NonAssocRing S] [Pow S ℕ] [NatPowAssoc S] [CommRing R]
    [Module R S] (p q : R[X]) (x : S) : (p - q).smeval x = p.smeval x - q.smeval x := by
  rw [sub_eq_add_neg, smeval_add, smeval_neg, sub_eq_add_neg]

end test
