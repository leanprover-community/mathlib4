/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.PNatPowAssoc
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Polynomial.Eval

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

## Things I need

* I should make a ncpoly class, for polynomials with no constant.  Notation should be `XR[X]`.  For
now we use `Finsupp` ℕ+ →₀ R, so `p.support` is a `Finset ℕ+`, `p.sum` is a sum over that.  Maybe
write a function that restricts a polynomial to a ncpoly, and one that extends a ncpoly to poly.

Reminder: A Non-unital non-associative `R`-algebra `A` is defined by the combination
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

/-- Evaluate a Finsupp `p` on `ℕ+` in the scalar commutative semiring `R` (essentially a polynomial
with vanishing constant term) at an element `x` in the target object `S` with scalar multiplication
by `R`. -/
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
