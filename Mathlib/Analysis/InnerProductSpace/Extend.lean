/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!

# Extension of isometries on Hilbert spaces

We construct the extension of a linear equivalence that is an isometry between dense subspaces of
two Hilbert spacse to the entire Hilbert space.

* `LinearEquiv.extendOfIsometry`: Extend `f : E ≃ₗ[𝕜] F` to a linear isometry equivalence
`Eₗ →ₗᵢ[𝕜] Fₗ`, where `e₁ : E →ₗ[𝕜] Eₗ` and `e₂ : F →ₗ[𝕜] Fₗ` are dense maps into Hilbert spaces
and `f` preserves the norm.

-/
@[expose] public section

suppress_compilation

variable {𝕜 E Eₗ F Fₗ : Type*}

namespace LinearEquiv

variable [RCLike 𝕜]
  [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]
  [NormedAddCommGroup Eₗ] [InnerProductSpace 𝕜 Eₗ] [CompleteSpace Eₗ]
  [NormedAddCommGroup Fₗ] [InnerProductSpace 𝕜 Fₗ] [CompleteSpace Fₗ]

variable (f : E ≃ₗ[𝕜] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜] Fₗ)

/-- Extend a densely defined operator that preserves the norm to a linear isometry equivalence. -/
def extendOfIsometry (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) :
    Eₗ ≃ₗᵢ[𝕜] Fₗ :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x ↦ by simpa using (h_norm (f.symm x)).symm
  (f.extend e₁ e₂ h_dense₁ (by use 1; simp [h_norm]) h_dense₂
    (by use 1; simp [h_norm₂])).toLinearEquiv.isometryOfInner (by
      rw [← LinearMap.norm_map_iff_inner_map_map]
      refine h_dense₁.induction ?_ (isClosed_eq ?_ continuous_norm)
      · intro x ⟨y, hxy⟩
        rw [← hxy]
        convert h_norm y
        apply LinearMap.extendOfNorm_eq h_dense₁ (by use 1; simp [h_norm])
      · apply (ContinuousLinearEquiv.continuous_toFun _).norm)

theorem extendOfIsometry_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm₁ : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : E) :
    f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm₁ (e₁ x) = e₂ (f x) :=
  LinearMap.extendOfNorm_eq h_dense₁ ⟨1, fun x ↦ by simp [h_norm₁ x]⟩ x

theorem extendOfIsometry_symm_eq (h_dense₁ : DenseRange e₁) (h_dense₂ : DenseRange e₂)
    (h_norm : ∀ x, ‖e₂ (f x)‖ = ‖e₁ x‖) (x : F) :
    (f.extendOfIsometry e₁ e₂ h_dense₁ h_dense₂ h_norm).symm (e₂ x) = e₁ (f.symm x) :=
  have h_norm₂ : ∀ x, ‖e₁ (f.symm x)‖ = ‖e₂ x‖ :=
    fun x ↦ by simpa using (h_norm (f.symm x)).symm
  LinearMap.extendOfNorm_eq h_dense₂ ⟨1, fun x ↦ by simp [h_norm₂ x]⟩ x

end LinearEquiv
