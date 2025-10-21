/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
-/
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
/-!
# Univariate skew polynomials

Given a ring `R` and an endomorphism `φ` on `R` the skew polynomials over `R`
are polynomials
$$\sum_{i= 0}^n a_iX^n, n\geq 0, a_i\in R$$
where the addition is the usual addition of polynomials
$$\sum_{i= 0}^n a_iX^n + \sum_{i= 0}^n b_iX^n= \sum_{i= 0}^n (a_i + b_i)X^n.$$
The multiplication, however, is determined by
$$Xa = \varphi (a)X$$
by extending it to all polynomials in the obvious way.

Skew polynomials are represented as `SkewMonoidAlgebra R (Multiplicative ℕ)`,
where `R` is usually at least a Semiring. In this file, we define `SkewPolynomial`
and provide basic instances.

**Note**: To register the endomorphism `φ` see notation below.

## Notation

The endomorphism `φ` is implemented using some action of `Multiplicative ℕ` on `R`.
From this action, `φ` is an `abbrev` denoting $(\text{ofAdd } 1) \cdot a := \varphi(a)$.

Users that want to work with a specific map `φ` should introduce an an action of
`Multiplicative ℕ` on `R`. Specifying that this action is a `MulSemiringAction` amount
to saying that `φ` is an endomorphism.

Furthermore, with this notation `φ^[n](a) = (ofAdd n) • a`, see `φ_iterate_apply`.

## Implementation notes

The implementation uses `Muliplicative ℕ` instead of `ℕ` as some notion
of `AddSkewMonoidAlgebra` like the current implementation of `Polynomials` in Mathlib.

This decision was made for two reasons:
  - To not have to create two essentially equivalent notions of
    skew monoid algebras - one additive and one multiplicative
  - Because we use the type class `MulSemiringAction` to specify the properties
  the action needs to respects for associativity. There are no version of this that
  uses an acting `AddMonoid M` and so we need to use `Multiplicative ℕ` for the action anyways.

For associativity to hold, there should be an instance of
`MulSemiringAction (Multiplicative ℕ) R` present in the context.
For example, in the context of $\mathbb{F}_q$-linear polynomials, this can be the
$q$-th Frobenius endomorphism - so $\varphi(a) = a^q$.

## Reference

The definition is inspired of [Papikian2023].

## Tags

Skew Polynomials, Twisted Polynomials.

## TODO :
  - Add algebra instance
  - Add `ext` lemma in terms of `Coeff`.
-/

noncomputable section

open Multiplicative SkewMonoidAlgebra

/-- The skew polynomials over `R` is the type of univariate polynomials over `R`
endowed with a skewed convolution product. -/
def SkewPolynomial (R : Type*) [AddCommMonoid R] := SkewMonoidAlgebra R (Multiplicative ℕ)

namespace SkewPolynomial
variable {R : Type*}

section Semiring
variable [Semiring R] {p q : SkewPolynomial R}

instance : Inhabited (SkewPolynomial R) := SkewMonoidAlgebra.instInhabited

instance : AddCommMonoid (SkewPolynomial R) := SkewMonoidAlgebra.instAddCommMonoid

instance instSemiring [MulSemiringAction (Multiplicative ℕ) R] : Semiring (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSemiring

variable {S S₁ S₂ : Type*}

instance [Semiring S] [Module S R] : Module S (SkewPolynomial R) :=
  SkewMonoidAlgebra.instModule

instance [Semiring S₁] [Semiring S₂] [Module S₁ R] [Module S₂ R]
    [SMulCommClass S₁ S₂ R] : SMulCommClass S₁ S₂ (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSMulCommClass

instance [SMulZeroClass S R] : SMulZeroClass S (SkewPolynomial R) :=
  SkewMonoidAlgebra.instSMulZeroClass

instance [SMul S₁ S₂] [SMulZeroClass S₁ R] [SMulZeroClass S₂ R]
    [IsScalarTower S₁ S₂ R] : IsScalarTower S₁ S₂ (SkewPolynomial R) :=
  SkewMonoidAlgebra.instIsScalarTower

instance [Subsingleton R] : Unique (SkewPolynomial R) :=
  SkewMonoidAlgebra.instUniqueOfSubsingleton

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support (p : SkewPolynomial R) : Finset ℕ := SkewMonoidAlgebra.support p

@[simp] lemma support_zero : (0 : SkewPolynomial R).support = ∅ := rfl

@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 := by
  simp [support]

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 := by
  simp

lemma support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simp [support, ← support_toFinsupp, toFinsupp_add p q, Finsupp.support_add]

section phi

variable [MulSemiringAction (Multiplicative ℕ) R]

/-- Ring homomorphism associated to the twist of the skew polynomial ring.
The multiplication in a skew polynomial ring is given by `xr = φ(r)x`. -/
abbrev φ := MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1)

theorem φ_def : φ = MulSemiringAction.toRingHom (Multiplicative ℕ) R (ofAdd 1) := rfl

lemma φ_iterate_apply (n : ℕ) (a : R) : (φ^[n] a) = ((ofAdd n) • a) := by
  induction n with
  | zero => simp
  | succ n hn =>
      simp_all [MulSemiringAction.toRingHom_apply, Function.iterate_succ', -Function.iterate_succ,
      ← mul_smul, mul_comm]

end phi

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] SkewPolynomial R := lsingle (ofAdd n)

lemma monomial_zero_right (n : ℕ) : monomial n (0 : R) = 0 := single_zero _

lemma monomial_zero_one [MulSemiringAction (Multiplicative ℕ) R] :
  monomial (0 : ℕ) (1 : R) = 1 := by rfl

lemma monomial_def (n : ℕ) (a : R) : monomial n a = single (ofAdd n) a := rfl

lemma monomial_add (n : ℕ) (r s : R) :
    monomial n (r + s) = monomial n r + monomial n s :=
  single_add ..

lemma smul_monomial {S} [Semiring S] [Module S R] (a : S) (n : ℕ) (b : R) :
    a • monomial n b = monomial n (a • b) :=
  smul_single ..

lemma monomial_mul_monomial [MulSemiringAction (Multiplicative ℕ) R] (n m : ℕ) (r s : R) :
    monomial n r * monomial m s = monomial (n + m) (r * (φ^[n] s)) := by
  rw [φ_iterate_apply]
  exact SkewMonoidAlgebra.single_mul_single

end Semiring

end SkewPolynomial
