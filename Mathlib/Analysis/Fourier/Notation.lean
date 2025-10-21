/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Algebra.Module.LinearMap.Defs

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

class FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F]
  extends FourierTransform E F where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

attribute [simp] FourierModule.fourier_add
attribute [simp] FourierModule.fourier_smul

variable {R E F : Type*} [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
  [FourierModule R E F]

variable (R E F)
def fourierₗ : E →ₗ[R] F where
  toFun := 𝓕
  map_add' := FourierModule.fourier_add
  map_smul' := FourierModule.fourier_smul

@[simp]
lemma FourierTransform.fourier_zero : 𝓕 (0 : E) = 0 := (fourierₗ R E F).map_zero

end add

section pair

open FourierTransform

class FourierPair (E F : Type*) extends FourierTransform E F, FourierTransformInv F E where
  inv_fourier : ∀ (f : E), 𝓕⁻ (𝓕 f) = f

class FourierPairInv (E F : Type*) extends FourierTransform E F, FourierTransformInv F E where
  fourier_inv : ∀ (f : F), 𝓕 (𝓕⁻ f) = f

attribute [simp] FourierPair.inv_fourier
attribute [simp] FourierPairInv.fourier_inv

end pair
