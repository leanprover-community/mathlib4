/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Topology.Algebra.Module.TensorProduct.Projective
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Analysis.Normed.Group.Basic
/-!
# Nuclear operators
TODO
-/
@[expose] public section

open TensorProduct UniformSpace ContinuousLinearMap

-- variable {𝕜 E F : Type*}
-- variable [CommSemiring R] [TopologicalSpace R]
-- variable [PartialOrder R]
-- variable [AddCommGroup M] [Module R M] [TopologicalSpace M] [LocallyConvexSpace R M]
-- variable [AddCommGroup N] [Module R N] [TopologicalSpace N] [LocallyConvexSpace R N]

variable {𝕜 X Y Z : Type*}

-- variable [CommSemiring 𝕜]
-- variable [Field 𝕜]
-- variable [NormedField 𝕜]
variable [NontriviallyNormedField 𝕜]
variable [TopologicalSpace 𝕜]
variable [PartialOrder 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] -- [ContinuousConstSMul 𝕜 E] -- [LocallyConvexSpace 𝕜 E]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y] -- [ContinuousConstSMul 𝕜 E]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z] -- [ContinuousConstSMul 𝕜 E]

#check X ⊗[𝕜]π Y
#synth UniformSpace (X ⊗[𝕜]π Y)
#check Completion (X ⊗[𝕜]π Y)

#check (smulRightL 𝕜 X Y)

#check (smulRightL 𝕜 X Y)

#check lift.equiv
#check (lift.equiv (RingHom.id 𝕜) X Y Z)

#check lift.equiv 𝕜 F (StrongDual 𝕜 E) (E →L[𝕜] F) (smulRightL 𝕜 E F).flip

variable (f : X →L[𝕜] Y →L[𝕜] Z) in
#check LinearMap.mkContinuous (𝕜 := 𝕜) (𝕜₂ := 𝕜) (E := X ⊗[𝕜] Y) (F := Z)
  (lift (toLinearMap₁₂ f))

/-- The linear equivalence between `ContinuousMultilinearMap 𝕜 E F` and `(⨂[𝕜] i, Eᵢ) →L[𝕜] F`
induced by `PiTensorProduct.lift`, for every normed space `F`.
The continuous version of `TensorProduct.lift.equiv`. -/
@[simps]
noncomputable def liftEquiv : (X →L[𝕜] Y →L[𝕜] Z) ≃ₗ[𝕜] (X ⊗[𝕜]π Y →L[𝕜] Z) where
  toFun f := LinearMap.mkContinuous (lift (toLinearMap₁₂ f)) ‖f‖ (by sorry)
  -- We use the algebraic `.symm` on the linear map coercion of `l`
  invFun l := LinearMap.mkContinuous₂ ((TensorProduct.lift.equiv (RingHom.id 𝕜) X Y Z).symm l.toLinearMap) sorry (by sorry)
  left_inv f := sorry-- by ext; simp
  right_inv l := sorry --by rw [← ContinuousLinearMap.coe_inj]; ext; simp
  map_add' f g := sorry -- by ext; simp
  map_smul' a f := sorry --by ext; simp


noncomputable def gamma : Y ⊗[𝕜] (StrongDual 𝕜 X) →L[𝕜] (X →L[𝕜] Y) :=
  liftEquiv 𝕜 Y (StrongDual 𝕜 X) (X →L[𝕜] Y) (smulRightL 𝕜 X Y).flip
