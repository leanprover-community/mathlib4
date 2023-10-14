/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Richard Hill
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Polynomial.Module
import Mathlib.Logic.Equiv.TransferInstance
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

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M] (d : Derivation R A M) (a : A)

open Polynomial Module

/--
For a derivation `d : A → M` and an element `a : A`, `d.comp_aeval a` is the
derivation of `R[X]` which takes a polynomial `f` to `d(aeval a f)`.

This derivation takes values in `comp_aeval R M a`, which is `M`, regarded as an
`R[X]`-module, with the action of a polynomial `f` defined by `f • m = (aeval a f) • m`.
-/
def comp_aeval : Derivation R R[X] <| CompAEval R M a where
  toFun f          := ⟨d (aeval a f)⟩
  map_add' _ _     := by simp [Equiv.add_def]
  map_smul' _ _    := by simp [Equiv.smul_def]
  leibniz' f g     := by simp [Equiv.add_def, Equiv.smul_def]
  map_one_eq_zero' := by simp [Equiv.zero_def]

lemma comp_aeval_apply (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = (d.comp_aeval a f).val := by rfl

lemma comp_aeval_apply' (d : Derivation R A M) (f : R[X]) :
    d.comp_aeval a f = ⟨d (aeval a f)⟩ := by rfl

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in the `R[X]`-module `CompAEval R M a`.
  For the same equation in `M`, see `Derivation.comp_aeval_eq`.
-/
theorem comp_aeval_eq' (d : Derivation R A M) (f : R[X]) :
    d.comp_aeval a f = (derivative f) • ⟨d a⟩ := by
  rw [←mkDerivation_apply]
  congr
  apply derivation_ext
  rw [comp_aeval_apply', aeval_X, mkDerivation_X]

/--
  A form of the chain rule: if `f` is a polynomial over `R`
  and `d : A → M` is an `R`-derivation then for all `a : A` we have
  $$ d(f(a)) = f' (a) d a. $$
  The equation is in `M`. For the same equation in `CompAEval R M a`,
  see `Derivation.comp_aeval'`.
-/
theorem comp_aeval_eq (d : Derivation R A M) (f : R[X]) :
    d (aeval a f) = aeval a (derivative f) • d a := by
  simp [comp_aeval_apply, comp_aeval_eq', CompAEval.smul_def, Equiv.smul_def]
