/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.LinearMap

variable {𝕜 E Eₗ F Fₗ : Type*}

namespace LinearEquiv

variable [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  [NormedAddCommGroup Eₗ] [InnerProductSpace 𝕜 Eₗ] [CompleteSpace Eₗ]
  [NormedAddCommGroup Fₗ] [InnerProductSpace 𝕜 Fₗ] [CompleteSpace Fₗ]

variable (f : E ≃ₗ[𝕜] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜] Fₗ)

/-- Extend a densely defined operator that preserves the norm to a linear isometry equivalence. -/
noncomputable
def extendOfIsometry (h_inj1 : LinearMap.ker e₁ = ⊥) (h_dense1 : DenseRange e₁)
    (h_norm1 : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (h_inj2 : LinearMap.ker e₂ = ⊥)
    (h_dense2 : DenseRange e₂) (h_norm2 : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖) :
    Eₗ ≃ₗᵢ[𝕜] Fₗ :=
  (f.extend e₁ e₂ h_inj1 h_dense1 (by use 1; simp [h_norm1]) h_inj2 h_dense2
    (by use 1; simp [h_norm2])).toLinearEquiv.isometryOfInner (by
      rw [← LinearMap.norm_map_iff_inner_map_map]
      refine h_dense1.induction ?_ (isClosed_eq ?_ continuous_norm)
      · intro x ⟨y, hxy⟩
        rw [← hxy]
        convert h_norm1 y
        apply LinearMap.extendOfNorm_eq h_inj1 h_dense1 (by use 1; simp [h_norm1])
      · apply (ContinuousLinearEquiv.continuous_toFun _).norm)

end LinearEquiv
