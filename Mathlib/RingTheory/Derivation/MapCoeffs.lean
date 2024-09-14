/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Derivation

/-!
# Coefficient-wise derivation on polynomials

In this file we define applying a derivation on the coefficients of a polynomial,
show this forms a derivation, and prove `apply_eval_eq`, which shows that for a derivation `D`,
`D(p(x)) = (D.mapCoeffs p)(x) + D(x) * p'(x)`. `apply_aeval_eq` and `apply_aeval_eq'`
are generalizations of that for algebras. We also have a special case for `DifferentialAlgebra`s.
-/

noncomputable section

open Polynomial Module

namespace Derivation

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] (d : Derivation R A M) (a : A)

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

namespace Differential

variable {A : Type*} [CommRing A] [Differential A]
variable {K : Type*} [Field K] [Differential K]

/--
A specialization of `Derivation.mapCoeffs` for the case of a differential ring.
-/
def mapCoeffs : Derivation ℤ A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]
lemma mapCoeffs_apply (p : A[X]) (i) :
    coeff (mapCoeffs p) i = (coeff p i)′ := rfl

@[simp]
lemma mapCoeffs_monomial (n : ℕ) (x : A) :
    mapCoeffs (monomial n x) = monomial n x′ := by
  simp [mapCoeffs]

@[simp]
lemma mapCoeffs_X :
    mapCoeffs (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

@[simp]
lemma mapCoeffs_C (x : A) :
    mapCoeffs (C x) = C x′ := by simp [← monomial_zero_left]

variable {R : Type*} [CommRing R] [Differential R] [Algebra A R] [DifferentialAlgebra A R]

theorem deriv_aeval_eq (x : R) (p : A[X]) :
    (aeval x p)′ = aeval x (mapCoeffs p) + aeval x (derivative p) * x′ := by
  convert Derivation.apply_aeval_eq' Differential.deriv _ (Algebra.linearMap A R) ..
  · simp [mapCoeffs]
  · simp [deriv_algebraMap]

def implicitDeriv (v : A[X]) :
    Derivation ℤ A[X] A[X] :=
  mapCoeffs + v • derivative'.restrictScalars ℤ

@[simp]
lemma implicitDeriv_C (v : A[X]) (b : A) :
    implicitDeriv v (C b) = C b′ := by
  unfold implicitDeriv
  simp

variable (A) in
def implicitDeriv' {K : Type*} [Field K] [Algebra A K] (x : K) : K :=
  - (aeval x (mapCoeffs (minpoly A x))) / (aeval x (derivative (minpoly A x)))

variable {R : Type*} [CommRing R] [Differential R] [Algebra K R] [DifferentialAlgebra K R]

lemma deriv_aeval_eq_implicitDeriv (x : R) (v : K[X]) (h : x′ = aeval x v) (p : K[X]) :
    (aeval x p)′ = aeval x (implicitDeriv v p) := by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

variable [CharZero K]

lemma deriv_eq_implicitDeriv' {F : Type*} [Field F] [Differential F] [Algebra K F]
    [DifferentialAlgebra K F] (x : F) (h : IsIntegral K x) :
    x′ = implicitDeriv' K x := by
  have := deriv_aeval_eq x (minpoly K x)
  simp only [minpoly.aeval, map_zero] at this
  simp [implicitDeriv']
  have _ : aeval x (derivative (minpoly K x)) ≠ 0 := by
    intro nh
    absurd minpoly.degree_le_of_ne_zero K x (fun h2 ↦ ((minpoly.natDegree_pos h).trans_eq
      (natDegree_eq_zero_of_derivative_eq_zero h2)).false) nh
    simp only [not_le]
    apply Polynomial.degree_derivative_lt
    exact minpoly.ne_zero h
  field_simp
  linear_combination -this

variable {R' : Type*} [CommRing R'] [Differential R'] [Algebra K R'] [DifferentialAlgebra K R']
variable [IsLeftCancelMulZero R'] [Nontrivial R]

lemma algHom_deriv (f : R →ₐ[K] R') (hf : Function.Injective f) (x : R) (h : IsIntegral K x) :
    f (x′) = (f x)′ := by
  let p := minpoly K x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · intro nh
    have := minpoly.degree_le_of_ne_zero K (f x) (fun h2 ↦ ((minpoly.natDegree_pos h).trans_eq
      (natDegree_eq_zero_of_derivative_eq_zero h2)).false) nh
    absurd minpoly.algHom_eq f hf x ▸ this
    simp only [not_le]
    apply Polynomial.degree_derivative_lt
    exact minpoly.ne_zero h
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp [← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

lemma algEquiv_deriv (f : R ≃ₐ[K] R') (x : R) (h : IsIntegral K x) :
    f (x′) = (f x)′ := algHom_deriv f.toAlgHom f.injective x h

variable [Algebra.IsIntegral K R]

lemma algHom_deriv' (f : R →ₐ[K] R') (hf : Function.Injective f) (x : R) :
    f (x′) = (f x)′ := algHom_deriv f hf x (Algebra.IsIntegral.isIntegral x)

lemma algEquiv_deriv' (f : R ≃ₐ[K] R') (x : R) :
    f (x′) = (f x)′ := algHom_deriv' f.toAlgHom f.injective x

end Differential
