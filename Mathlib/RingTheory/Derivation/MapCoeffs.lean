/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Module.Basic

/-!
# Coefficient-wise derivation on polynomials

In this file we define applying a derivation on the coefficients of a polynomial,
show this forms a derivation, and prove `apply_eval_eq`, which shows that for a derivation `D`,
`D(p(x)) = (D.mapCoeffs p)(x) + D(x) * p'(x)`. `apply_aeval_eq` and `apply_aeval_eq'`
are generalizations of that for algebras.
-/

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M)

/--
The `R`-derivation from `A[X]` to `M[X]` which applies the derivative to each
of the coefficients.
-/
def mapCoeffs : Derivation R A[X] (PolynomialModule A M) where
  __ := (PolynomialModule.map A d.toLinearMap).comp
    PolynomialModule.equivPolynomial.symm.toLinearMap
  map_one_eq_zero' := show (Finsupp.single 0 1).mapRange (d : A → M) d.map_zero = 0 by simp
  leibniz' p q := by
    dsimp
    induction p using Polynomial.induction_on' with
    | h_add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | h_monomial n a =>
      induction q using Polynomial.induction_on' with
      | h_add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | h_monomial m b =>
        refine Finsupp.ext fun i ↦ ?_
        dsimp [PolynomialModule.equivPolynomial, PolynomialModule.map]
        simp only [toFinsupp_mul, toFinsupp_monomial, AddMonoidAlgebra.single_mul_single]
        show d _ = _ + _
        erw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply]
        rw [Finsupp.mapRange_single, Finsupp.mapRange_single]
        erw [PolynomialModule.monomial_smul_single, PolynomialModule.monomial_smul_single]
        simp only [AddMonoidAlgebra.single_apply, apply_ite d, leibniz, map_zero, coeFn_coe,
          PolynomialModule.single_apply, ite_add_zero, add_comm m n]

@[simp]
lemma mapCoeffs_apply (p : A[X]) (i) :
    d.mapCoeffs p i = d (coeff p i) := rfl

@[simp]
lemma mapCoeffs_monomial (n : ℕ) (x : A) :
    d.mapCoeffs (monomial n x) = .single A n (d x) := Finsupp.ext fun _ ↦ by
  simp [coeff_monomial, apply_ite d, PolynomialModule.single_apply]

@[simp]
lemma mapCoeffs_X :
    d.mapCoeffs (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

@[simp]
lemma mapCoeffs_C (x : A) :
    d.mapCoeffs (C x) = .single A 0 (d x) := by simp [← monomial_zero_left]

variable {B M' : Type*} [CommRing B] [Algebra R B] [Algebra A B]
    [AddCommGroup M'] [Module B M'] [Module R M'] [Module A M']

theorem apply_aeval_eq' (d' : Derivation R B M') (f : M →ₗ[A] M')
    (h : ∀ a, f (d a) = d' (algebraMap A B a)) (x : B) (p : A[X]) :
    d' (aeval x p) = PolynomialModule.eval x (PolynomialModule.map B f (d.mapCoeffs p)) +
      aeval x (derivative p) • d' x := by
  induction p using Polynomial.induction_on' with
  | h_add => simp_all only [eval_add, map_add, add_smul]; abel
  | h_monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, mapCoeffs_monomial,
      PolynomialModule.map_single, PolynomialModule.eval_single, derivative_monomial, map_mul,
      _root_.map_natCast, h]
    rw [add_comm, ← smul_smul, ← smul_smul, Nat.cast_smul_eq_nsmul]


theorem apply_aeval_eq [IsScalarTower R A B] [IsScalarTower A B M'] (d : Derivation R B M')
    (x : B) (p : A[X]) :
    d (aeval x p) = PolynomialModule.eval x ((d.compAlgebraMap A).mapCoeffs p) +
      aeval x (derivative p) • d x := by
  convert apply_aeval_eq' (d.compAlgebraMap A) d LinearMap.id _ x p
  · apply Finsupp.ext
    intro x
    rfl
  · intro a
    rfl

theorem apply_eval_eq (x : A) (p : A[X]) :
    d (eval x p) = PolynomialModule.eval x (d.mapCoeffs p) + eval x (derivative p) • d x :=
  apply_aeval_eq d x p

end Derivation
