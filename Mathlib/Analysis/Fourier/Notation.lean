/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Algebra.Module.LinearMap.Defs

/-! # Type classes for the Fourier transform

In this file we define type classes for the Fourier transform and the inverse Fourier transform.
We introduce the notation `𝓕` and `𝓕⁻` in these classes to denote the Fourier transform and
the inverse Fourier transform, respectively.

Moreover, we provide type-classes that encode the linear structure and the Fourier inversion
theorem.
-/

universe u v w

/--
The notation typeclass for the Fourier transform.
-/
class FourierTransform (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕 f` is the Fourier transform of `f`. The meaning of this notation is type-dependent. -/
  fourierTransform : E → F

/--
The notation typeclass for the inverse Fourier transform.
-/
class FourierTransformInv (E : Type u) (F : outParam (Type v)) where
  /-- `𝓕⁻ f` is the inverse Fourier transform of `f`. The meaning of this notation is
  type-dependent. -/
  fourierTransformInv : E → F

namespace FourierTransform

@[inherit_doc] scoped notation "𝓕" => FourierTransform.fourierTransform
@[inherit_doc] scoped notation "𝓕⁻" => FourierTransformInv.fourierTransformInv

end FourierTransform

section add

open FourierTransform

/-- A `FourierModule` is a function space on which the Fourier transform is a linear map. -/
class FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransform E F where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

attribute [simp] FourierModule.fourier_add
attribute [simp] FourierModule.fourier_smul

/-- A `FourierInvModule` is a function space on which the Fourier transform is a linear map. -/
class FourierInvModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransformInv E F where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

attribute [simp] FourierInvModule.fourierInv_add
attribute [simp] FourierInvModule.fourierInv_smul

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]

variable (R E F) [FourierModule R E F] in
/-- The Fourier transform as a linear map. -/
def fourierₗ : E →ₗ[R] F where
  toFun := 𝓕
  map_add' := FourierModule.fourier_add
  map_smul' := FourierModule.fourier_smul

@[simp]
lemma FourierTransform.fourier_zero [FourierModule R E F] : 𝓕 (0 : E) = 0 :=
  (fourierₗ R E F).map_zero

variable (R E F) [FourierInvModule R E F] in
/-- The inverse Fourier transform as a linear map. -/
def fourierInvₗ : E →ₗ[R] F where
  toFun := 𝓕⁻
  map_add' := FourierInvModule.fourierInv_add
  map_smul' := FourierInvModule.fourierInv_smul

@[simp]
lemma FourierTransform.fourierInv_zero [FourierInvModule R E F] : 𝓕⁻ (0 : E) = 0 :=
  (fourierInvₗ R E F).map_zero

end add

section pair

open FourierTransform

/-- A `FourierPair` is a pair of spaces `E` and `F` such that `𝓕⁻ ∘ 𝓕 = id` on `E`. -/
class FourierPair (E F : Type*) extends FourierTransform E F, FourierTransformInv F E where
  inv_fourier : ∀ (f : E), 𝓕⁻ (𝓕 f) = f

/-- A `FourierPairInv` is a pair of spaces `E` and `F` such that `𝓕 ∘ 𝓕⁻ = id` on `F`. -/
class FourierPairInv (E F : Type*) extends FourierTransform E F, FourierTransformInv F E where
  fourier_inv : ∀ (f : F), 𝓕 (𝓕⁻ f) = f

attribute [simp] FourierPair.inv_fourier
attribute [simp] FourierPairInv.fourier_inv

end pair
