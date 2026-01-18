/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Type classes for the Fourier transform

In this file we define type classes for the Fourier transform and the inverse Fourier transform.
We introduce the notation `𝓕` and `𝓕⁻` in these classes to denote the Fourier transform and
the inverse Fourier transform, respectively.

Moreover, we provide type-classes that encode the linear structure and the Fourier inversion
theorem.
-/

@[expose] public section

universe u v w

variable {R E F : Type*}

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

/-- A `FourierAdd` is a function space on which the Fourier transform is additive. -/
class FourierAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransform E F] where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g

/-- A `FourierSMul` is a function space on which the Fourier transform is homogeneous. -/
class FourierSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransform E F] where
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- The Fourier transform is continuous. -/
class ContinuousFourier (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransform E F] where
  continuous_fourier : Continuous (𝓕 : E → F)

/-- A `FourierInvAdd` is a function space on which the inverse Fourier transform is additive. -/
class FourierInvAdd (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [FourierTransformInv E F]
    where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g

/-- A `FourierInvSMul` is a function space on which the inverse Fourier transform is homogeneous. -/
class FourierInvSMul (R : Type*) (E : Type*) (F : outParam (Type*)) [SMul R E] [SMul R F]
    [FourierTransformInv E F] where
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

/-- The inverse Fourier transform is continuous. -/
class ContinuousFourierInv (E : Type*) (F : outParam (Type*))
    [TopologicalSpace E] [TopologicalSpace F] [FourierTransformInv E F] where
  continuous_fourierInv : Continuous (𝓕⁻ : E → F)

/-- A `FourierModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierAdd` and `FourierSMul` instead" (since := "2026-01-06")]
structure FourierModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransform E F where
  fourier_add : ∀ (f g : E), 𝓕 (f + g) = 𝓕 f + 𝓕 g
  fourier_smul : ∀ (r : R) (f : E), 𝓕 (r • f) = r • 𝓕 f

/-- A `FourierInvModule` is a function space on which the Fourier transform is a linear map. -/
@[deprecated "use `FourierInvAdd` and `FourierInvSMul` instead" (since := "2026-01-06")]
structure FourierInvModule (R : Type*) (E : Type*) (F : outParam (Type*)) [Add E] [Add F] [SMul R E]
    [SMul R F] extends FourierTransformInv E F where
  fourierInv_add : ∀ (f g : E), 𝓕⁻ (f + g) = 𝓕⁻ f + 𝓕⁻ g
  fourierInv_smul : ∀ (r : R) (f : E), 𝓕⁻ (r • f) = r • 𝓕⁻ f

namespace FourierTransform

export FourierAdd (fourier_add)
export FourierSMul (fourier_smul)
export ContinuousFourier (continuous_fourier)
export FourierInvAdd (fourierInv_add)
export FourierInvSMul (fourierInv_smul)
export ContinuousFourierInv (continuous_fourierInv)

attribute [simp] fourier_add
attribute [simp] fourier_smul
attribute [simp] fourierInv_add
attribute [simp] fourierInv_smul
attribute [fun_prop] continuous_fourier
attribute [fun_prop] continuous_fourierInv

variable [Semiring R] [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]

section fourierCLM

variable [FourierTransform E F] [FourierAdd E F] [FourierSMul R E F]

variable (R E) in
/-- The Fourier transform as a linear map. -/
def fourierₗ : E →ₗ[R] F where
  toFun := 𝓕
  map_add' := fourier_add
  map_smul' := fourier_smul

@[simp]
lemma fourierₗ_apply (f : E) : fourierₗ R E f = 𝓕 f := rfl

include R in
variable (R) in
lemma fourier_zero : 𝓕 (0 : E) = 0 :=
  (fourierₗ R E).map_zero

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourier E F]

variable (R E) in
/-- The Fourier transform as a continuous linear map. -/
def fourierCLM : E →L[R] F where
  __ := fourierₗ R E
  cont := continuous_fourier

@[simp]
lemma fourierCLM_apply (f : E) : fourierCLM R E f = 𝓕 f := rfl

end fourierCLM

section fourierInvCLM

variable [FourierTransformInv E F] [FourierInvAdd E F] [FourierInvSMul R E F]

variable (R E) in
/-- The inverse Fourier transform as a linear map. -/
def fourierInvₗ : E →ₗ[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul

@[simp]
lemma fourierInvₗ_apply (f : E) : fourierInvₗ R E f = 𝓕⁻ f := rfl

include R in
variable (R) in
lemma fourierInv_zero : 𝓕⁻ (0 : E) = 0 :=
  (fourierInvₗ R E).map_zero

variable [TopologicalSpace E] [TopologicalSpace F] [ContinuousFourierInv E F]

variable (R E) in
/-- The inverse Fourier transform as a continuous linear map. -/
def fourierInvCLM : E →L[R] F where
  toFun := 𝓕⁻
  map_add' := fourierInv_add
  map_smul' := fourierInv_smul
  cont := continuous_fourierInv

@[simp]
lemma fourierInvCLM_apply (f : E) : fourierInvCLM R E f = 𝓕⁻ f := rfl

end fourierInvCLM

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
  [FourierTransform E F] [FourierAdd E F] [FourierSMul R E F]
  [FourierTransformInv F E]
  [FourierPair E F] [FourierInvPair F E]

variable (R E) in
/-- The Fourier transform as a linear equivalence. -/
def fourierEquiv : E ≃ₗ[R] F where
  __ := fourierₗ R E
  invFun := 𝓕⁻
  left_inv := fourierInv_fourier_eq
  right_inv := fourier_fourierInv_eq

@[simp]
lemma fourierEquiv_apply (f : E) : fourierEquiv R E f = 𝓕 f := rfl

@[simp]
lemma fourierEquiv_symm_apply (f : F) : (fourierEquiv R E).symm f = 𝓕⁻ f := rfl

variable [TopologicalSpace E] [TopologicalSpace F]
  [ContinuousFourier E F] [ContinuousFourierInv F E]

variable (R E) in
/-- The Fourier transform as a continuous linear equivalence. -/
def fourierCLE : E ≃L[R] F where
  __ := fourierEquiv R E
  continuous_toFun := continuous_fourier
  continuous_invFun := continuous_fourierInv

@[simp]
lemma fourierCLE_apply (f : E) : fourierCLE R E f = 𝓕 f := rfl

@[simp]
lemma fourierCLE_symm_apply (f : F) : (fourierCLE R E).symm f = 𝓕⁻ f := rfl

end FourierTransform

end Pair
