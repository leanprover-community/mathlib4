/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.Separable

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
    | add => simp only [add_mul, map_add, add_smul, smul_add, add_add_add_comm, *]
    | monomial n a =>
      induction q using Polynomial.induction_on' with
      | add => simp only [mul_add, map_add, add_smul, smul_add, add_add_add_comm, *]
      | monomial m b =>
        refine Finsupp.ext fun i ↦ ?_
        dsimp [PolynomialModule.equivPolynomial, PolynomialModule.map]
        simp only [toFinsupp_mul, toFinsupp_monomial, AddMonoidAlgebra.single_mul_single]
        show d _ = _ + _
        -- TODO: copy more `Finsupp` API to `PolynomialModule`.
        -- We have to do a bit of work to go through the identification
        -- `PolynomialModule A M = ℕ →₀ M`...
        dsimp only [PolynomialModule, Finsupp.mapRange.linearMap_apply, coeFn_coe]
        rw [Finsupp.mapRange_single, Finsupp.mapRange_single]
        -- ... and here we go back through the identification.
        show _ = (_ • PolynomialModule.single A _ _) _ + (_ • PolynomialModule.single A _ _) i
        simp only [PolynomialModule.monomial_smul_single, AddMonoidAlgebra.single_apply,
          apply_ite d, leibniz, map_zero, coeFn_coe, PolynomialModule.single_apply, ite_add_zero,
          add_comm m n]

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
  | add => simp_all only [eval_add, map_add, add_smul]; abel
  | monomial =>
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

/--
A specialization of `Derivation.mapCoeffs` for the case of a differential ring.
-/
def mapCoeffs : Derivation ℤ A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer Differential.deriv.mapCoeffs

@[simp]
lemma coeff_mapCoeffs (p : A[X]) (i) :
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

/--
The unique derivation which can be made to a `DifferentialAlgebra` on `A[X]` with
`X′ = v`.
-/
def implicitDeriv (v : A[X]) :
    Derivation ℤ A[X] A[X] :=
  mapCoeffs + v • derivative'.restrictScalars ℤ

@[simp]
lemma implicitDeriv_C (v : A[X]) (b : A) :
    implicitDeriv v (C b) = C b′ := by
  simp [implicitDeriv]

@[simp]
lemma implicitDeriv_X (v : A[X]) :
    implicitDeriv v X = v := by
  simp [implicitDeriv]

lemma deriv_aeval_eq_implicitDeriv (x : R) (v : A[X]) (h : x′ = aeval x v) (p : A[X]) :
    (aeval x p)′ = aeval x (implicitDeriv v p) := by
  simp [deriv_aeval_eq, implicitDeriv, h, mul_comm]

variable {R' : Type*} [CommRing R'] [Differential R'] [Algebra A R'] [DifferentialAlgebra A R']
variable [IsDomain R'] [Nontrivial R]

lemma algHom_deriv (f : R →ₐ[A] R') (hf : Function.Injective f) (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ := by
  let p := minpoly A x
  apply mul_left_cancel₀ (a := aeval (f x) (derivative p))
  · rw [Polynomial.aeval_algHom]
    simp only [AlgHom.coe_comp, Function.comp_apply, ne_eq, map_eq_zero_iff f hf]
    apply Separable.aeval_derivative_ne_zero h (minpoly.aeval A x)
  conv => lhs; rw [Polynomial.aeval_algHom]
  simp only [AlgHom.coe_comp, Function.comp_apply, ← map_mul]
  apply add_left_cancel (a := aeval (f x) (mapCoeffs p))
  rw [← deriv_aeval_eq]
  simp only [aeval_algHom, AlgHom.coe_comp, Function.comp_apply, ← map_add, ← deriv_aeval_eq,
    minpoly.aeval, map_zero, p]

omit [Nontrivial R] in
lemma algEquiv_deriv (f : R ≃ₐ[A] R') (x : R) (h : IsSeparable A x) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv f.toAlgHom f.injective x h

variable [Algebra.IsSeparable A R]

/--
`algHom_deriv` in a separable algebra
-/
lemma algHom_deriv' (f : R →ₐ[A] R') (hf : Function.Injective f) (x : R) :
    f (x′) = (f x)′ := algHom_deriv f hf x (Algebra.IsSeparable.isSeparable' x)

omit [Nontrivial R] in
/--
`algEquiv_deriv` in a separable algebra
-/
lemma algEquiv_deriv' (f : R ≃ₐ[A] R') (x : R) :
    f (x′) = (f x)′ :=
  haveI := f.nontrivial
  algHom_deriv' f.toAlgHom f.injective x

end Differential
