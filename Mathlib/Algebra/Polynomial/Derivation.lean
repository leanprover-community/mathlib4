/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard Hill
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Module.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.Derivation.Basic
/-!
# Derivations of univariate polynomials

In this file we prove that an `R`-derivation of `Polynomial R` is determined by its value on `X`.
We also provide a constructor `Polynomial.mkDerivation` that
builds a derivation from its value on `X`, and a linear equivalence
`Polynomial.mkDerivationEquiv` between `A` and `Derivation (Polynomial R) A`.
-/

noncomputable section

namespace Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R]

/-- `Polynomial.derivative` as a derivation. -/
@[simps]
def derivative' : Derivation R R[X] R[X] where
  toFun := derivative
  map_add' _ _ := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]

variable [AddCommMonoid A] [Module R A] [Module (Polynomial R) A]

@[simp]
theorem derivation_C (D : Derivation R R[X] A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
theorem C_smul_derivation_apply (D : Derivation R R[X] A) (a : R) (f : R[X]) :
    C a • D f = a • D f := by
  have : C a • D f = D (C a * f) := by simp
  rw [this, C_mul', D.map_smul]

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R R[X] A} (h : D₁ X = D₂ X) : D₁ = D₂ :=
  Derivation.ext fun f => Derivation.eqOn_adjoin (Set.eqOn_singleton.2 h) <| by
    simp only [adjoin_X, Algebra.coe_top, Set.mem_univ]

variable [IsScalarTower R (Polynomial R) A]
variable (R)

/-- The derivation on `R[X]` that takes the value `a` on `X`. -/
def mkDerivation : A →ₗ[R] Derivation R R[X] A where
  toFun := fun a ↦ (LinearMap.toSpanSingleton R[X] A a).compDer derivative'
  map_add' := fun a b ↦ by ext; simp
  map_smul' := fun t a ↦ by ext; simp

lemma mkDerivation_apply (a : A) (f : R[X]) :
    mkDerivation R a f = derivative f • a := by
  rfl

@[simp]
theorem mkDerivation_X (a : A) : mkDerivation R a X = a := by simp [mkDerivation_apply]

lemma mkDerivation_one_eq_derivative' : mkDerivation R (1 : R[X]) = derivative' := by
  ext : 1
  simp [derivative']

lemma mkDerivation_one_eq_derivative (f : R[X]) : mkDerivation R (1 : R[X]) f = derivative f := by
  rw [mkDerivation_one_eq_derivative']
  rfl

/-- `Polynomial.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : A ≃ₗ[R] Derivation R R[X] A :=
  LinearEquiv.symm <|
    { invFun := mkDerivation R
      toFun := fun D => D X
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_X _ _
      right_inv := fun _ => mkDerivation_X _ _ }

@[simp] lemma mkDerivationEquiv_apply (a : A) :
    mkDerivationEquiv R a = mkDerivation R a := by
  rfl

@[simp] lemma mkDerivationEquiv_symm_apply (D : Derivation R R[X] A) :
    (mkDerivationEquiv R).symm D = D X := rfl

end CommSemiring
end Polynomial

namespace Derivation

open Polynomial Module

section compAEval

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

/--
For a derivation `d : A → M` and an element `a : A`, `d.compAEval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `Module.AEval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
/-
Note: `compAEval` is not defined using `Derivation.compAlgebraMap`.
This because `A` is not an `R[X]` algebra and it would be messy to create an algebra instance
within the definition.
-/
@[simps]
def compAEval : Derivation R R[X] <| AEval R M a where
  toFun f          := AEval.of R M a (d (aeval a f))
  map_add'         := by simp
  map_smul'        := by simp
  leibniz'         := by simp [AEval.of_aeval_smul, -Derivation.map_aeval]
  map_one_eq_zero' := by simp

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in the `R[X]`-module `Module.AEval R M a`.
  For the same equation in `M`, see `Derivation.compAEval_eq`.
-/
theorem compAEval_eq (d : Derivation R A M) (f : R[X]) :
    d.compAEval a f = derivative f • (AEval.of R M a (d a)) := by
  rw [← mkDerivation_apply]
  congr
  apply derivation_ext
  simp

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in `M`. For the same equation in `Module.AEval R M a`,
  see `Derivation.compAEval_eq`.
-/
theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a :=
  calc
    _ = (AEval.of R M a).symm (d.compAEval a f) := rfl
    _ = _ := by simp [-compAEval_apply, compAEval_eq]

end compAEval

section coeffwise

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

/--
The `R`-derivation from `A[X]` to `M[X]` which applies the derivative to each
of the coefficients.
-/
def coeffwise : Derivation R A[X] (PolynomialModule A M) where
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
lemma coeffwise_apply (p : A[X]) (i) :
    d.coeffwise p i = d (coeff p i) := rfl

@[simp]
lemma coeffwise_monomial (n : ℕ) (x : A) :
    d.coeffwise (monomial n x) = .single A n (d x) := Finsupp.ext fun _ ↦ by
  simp [coeff_monomial, apply_ite d, PolynomialModule.single_apply]

@[simp]
lemma coeffwise_X :
    d.coeffwise (X : A[X]) = 0 := by simp [← monomial_one_one_eq_X]

@[simp]
lemma coeffwise_C (x : A) :
    d.coeffwise (C x) = .single A 0 (d x) := by simp [← monomial_zero_left]

variable {K : Type*} [CommRing K] [Algebra A K] [Algebra R K] [IsScalarTower R A K]
    [Module K M] [IsScalarTower A K M]

theorem apply_aeval_eq (d : Derivation R K M) (x : K) (p : A[X]) :
    d (aeval x p) = PolynomialModule.eval x ((d.compAlgebraMap A).coeffwise p) +
      aeval x (derivative p) • d x := by
  induction p using Polynomial.induction_on' with
  | h_add => simp_all only [eval_add, map_add, add_smul]; abel
  | h_monomial =>
    simp only [aeval_monomial, leibniz, leibniz_pow, algebraMap_smul, coeffwise_monomial,
      compAlgebraMap_apply, derivative_monomial, map_mul, _root_.map_natCast]
    erw [PolynomialModule.eval_single]
    rw [add_comm, ← smul_smul, ← smul_smul, ← nsmul_eq_smul_cast, algebraMap_smul]

theorem apply_eval_eq (x : A) (p : A[X]) :
    d (eval x p) = PolynomialModule.eval x (d.coeffwise p) + eval x (derivative p) • d x :=
  apply_aeval_eq d x p

end coeffwise

end Derivation
