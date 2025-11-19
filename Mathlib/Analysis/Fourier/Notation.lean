/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs

/-! # Type classes for the Fourier transform

In this file we define type classes for the Fourier transform and the inverse Fourier transform.
We introduce the notation `𝓕` and `𝓕⁻` in these classes to denote the Fourier transform and
the inverse Fourier transform, respectively.

Moreover, we provide type-classes that encode the linear structure and the Fourier inversion
theorem.
-/

@[expose] public section

universe u v w

/--
The notation typeclass for the Fourier transform.

While the Fourier transform is a linear operator, the notation is for the function `E → F` without
any additional properties. This makes it possible to use the notation for functions where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the notation type class.
-/
class FourierTransform (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕 f` is the Fourier transform of `f`. The meaning of this notation is type-dependent. -/
  fourier : E → F

/--
The notation typeclass for the inverse Fourier transform.

While the inverse Fourier transform is a linear operator, the notation is for the function `E → F`
without any additional properties. This makes it possible to use the notation for functions where
integrability is an issue.
Moreover, including a scalar multiplication causes problems for inferring the notation type class.
-/
class FourierTransformInv (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕⁻ f` is the inverse Fourier transform of `f`. The meaning of this notation is
  type-dependent. -/
  fourierInv : E → F

namespace FourierTransform

export FourierTransformInv (fourierInv)

@[inherit_doc] scoped notation "𝓕" => fourier
@[inherit_doc] scoped notation "𝓕⁻" => fourierInv

end FourierTransform

section Module

open scoped FourierTransform

/-- A `FourierModule` is a function space on which the Fourier transform is a linear map. -/
class FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransform E F where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- A `FourierInvModule` is a function space on which the Fourier transform is a linear map. -/
class FourierInvModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransformInv E F where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

namespace FourierTransform

export FourierModule (fourier_add fourier_smul)
export FourierInvModule (fourierInv_add fourierInv_smul)

attribute [simp] fourier_add
attribute [simp] fourier_smul
attribute [simp] FourierInvModule.fourierInv_add
attribute [simp] FourierInvModule.fourierInv_smul

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]

section fourierₗ

variable [FourierModule R E F]

variable (R E F) in
/-- The Fourier transform as a linear map. -/
def fourierₗ : E →ₗ[R] F where
  toFun := 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]
lemma fourierₗ_apply (f : E) : fourierₗ R E F f = 𝓕 f := rfl

@[simp]
lemma fourier_zero : 𝓕 (0 : E) = 0 :=
  (fourierₗ R E F).map_zero

end fourierₗ

section fourierInvₗ

variable [FourierInvModule R E F]

variable (R E F) in
/-- The inverse Fourier transform as a linear map. -/
def fourierInvₗ : E →ₗ[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
lemma fourierInvₗ_apply (f : E) : fourierInvₗ R E F f = 𝓕⁻ f := rfl

@[simp]
lemma fourierInv_zero : 𝓕⁻ (0 : E) = 0 :=
  (fourierInvₗ R E F).map_zero

end fourierInvₗ

end FourierTransform

end Module

section Pair

open FourierTransform

/-- A `FourierPair` is a pair of spaces `E` and `F` such that `𝓕⁻ ∘ 𝓕 = id` on `E`. -/
class FourierPair (E F : Type*) [FourierTransform E F] [FourierTransformInv F E] where
  fourierInv_fourier_eq : ∀ (f : E), 𝓕⁻ (𝓕 f) = f

/-- A `FourierInvPair` is a pair of spaces `E` and `F` such that `𝓕 ∘ 𝓕⁻ = id` on `E`. -/
class FourierInvPair (E F : Type*) [FourierTransform F E] [FourierTransformInv E F] where
  fourier_fourierInv_eq : ∀ (f : E), 𝓕 (𝓕⁻ f) = f

namespace FourierTransform

export FourierPair (fourierInv_fourier_eq)
export FourierInvPair (fourier_fourierInv_eq)

attribute [simp] fourierInv_fourier_eq
attribute [simp] fourier_fourierInv_eq

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  [FourierModule R E F] [FourierInvModule R F E] [FourierPair E F] [FourierInvPair F E]

variable (R E F) in
/-- The Fourier transform as a linear equivalence. -/
def fourierEquiv : E ≃ₗ[R] F where
  __ := fourierₗ R E F
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]
lemma fourierEquiv_apply (f : E) : fourierEquiv R E F f = 𝓕 f := rfl

@[simp]
lemma fourierEquiv_symm_apply (f : F) : (fourierEquiv R E F).symm f = 𝓕⁻ f := rfl

end FourierTransform

end Pair
