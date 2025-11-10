/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Topology.Algebra.Module.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# The topology of pointwise convergence is locally convex
-/

variable {𝕜₁ 𝕜₂ : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
variable {σ : 𝕜₁ →+* 𝕜₂}
variable {E F : Type*} [AddCommGroup E] [TopologicalSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜₂ F] [Module 𝕜₁ E]

namespace PointwiseConvergenceCLM

/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected def seminorm (x : E) : Seminorm 𝕜₂ (E →SLₚₜ[σ] F) where
  toFun A := ‖A x‖
  map_zero' := by simp
  add_le' A B := by simpa only using norm_add_le _ _
  neg' A := by simp
  smul' r A := by simp [norm_smul]

variable (σ E F) in
/-- The family of seminorms that induce the topology of pointwise convergence, namely `‖A x‖` for
all `x : E`. -/
protected def seminormFamily : SeminormFamily 𝕜₂ (E →SLₚₜ[σ] F) E :=
  PointwiseConvergenceCLM.seminorm

variable (σ E F) in
def inducingFn : (E →SLₚₜ[σ] F) →ₗ[𝕜₂] (E → F) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ E F) in
theorem inducingFn_isInducing : Topology.IsInducing (inducingFn σ E F) :=
  (PointwiseConvergenceCLM.isEmbedding_coeFn σ E F).isInducing

lemma withSeminorms : WithSeminorms (PointwiseConvergenceCLM.seminormFamily σ E F) :=
  let e : E ≃ (Σ _ : E, Fin 1) := .symm <| .sigmaUnique _ _
  (inducingFn_isInducing σ E F).withSeminorms <| withSeminorms_pi (fun _ ↦ norm_withSeminorms 𝕜₂ F)
    |>.congr_equiv e

variable [NormedSpace ℝ F] [NormedSpace ℝ 𝕜₂] [IsScalarTower ℝ 𝕜₂ F]

--instance instLocallyConvexSpace : LocallyConvexSpace ℝ (E →SLₚₜ[σ] F) :=
  --withSeminorms.toLocallyConvexSpace

end PointwiseConvergenceCLM
