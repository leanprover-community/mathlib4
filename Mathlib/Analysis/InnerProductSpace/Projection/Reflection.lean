/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Reflection

A linear isometry equivalence `K.reflection : E ≃ₗᵢ[𝕜] E` in constructed, by choosing
for each `u : E`, `K.reflection u = 2 • K.starProjection u - u`.
-/

noncomputable section

namespace Submodule

section reflection

open Submodule RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)
variable [K.HasOrthogonalProjection]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflectionLinearEquiv : E ≃ₗ[𝕜] E :=
  LinearEquiv.ofInvolutive
    (2 • (K.starProjection.toLinearMap) - LinearMap.id) fun x => by
    simp [two_smul, starProjection_eq_self_iff.mpr]

/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
def reflection : E ≃ₗᵢ[𝕜] E :=
  { K.reflectionLinearEquiv with
    norm_map' := by
      intro x
      let w : K := K.orthogonalProjection x
      let v := x - w
      have : ⟪v, w⟫ = 0 := starProjection_inner_eq_zero x w w.2
      convert norm_sub_eq_norm_add this using 2
      · dsimp [reflectionLinearEquiv, v, w]
        abel
      · simp only [v, add_sub_cancel] }

variable {K}

/-- The result of reflecting. -/
theorem reflection_apply (p : E) : K.reflection p = 2 • K.starProjection p - p :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm : K.reflection.symm = K.reflection :=
  rfl

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_inv : K.reflection⁻¹ = K.reflection :=
  rfl

variable (K)

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (p : E) : K.reflection (K.reflection p) = p :=
  K.reflection.left_inv p

/-- Reflection is involutive. -/
theorem reflection_involutive : Function.Involutive K.reflection :=
  K.reflection_reflection

/-- Reflection is involutive. -/
@[simp]
theorem reflection_trans_reflection :
    K.reflection.trans K.reflection = LinearIsometryEquiv.refl 𝕜 E :=
  LinearIsometryEquiv.ext <| reflection_involutive K

/-- Reflection is involutive. -/
@[simp]
theorem reflection_mul_reflection : K.reflection * K.reflection = 1 :=
  reflection_trans_reflection _
theorem reflection_orthogonal_apply (v : E) : Kᗮ.reflection v = -K.reflection v := by
  simp [reflection_apply]; abel

theorem reflection_orthogonal : Kᗮ.reflection = .trans K.reflection (.neg _) := by
  ext; apply reflection_orthogonal_apply

variable {K}

theorem reflection_singleton_apply (u v : E) :
    reflection (𝕜 ∙ u) v = 2 • (⟪u, v⟫ / ((‖u‖ : 𝕜) ^ 2)) • u - v := by
  rw [reflection_apply, starProjection_singleton, ofReal_pow]

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff (x : E) : K.reflection x = x ↔ x ∈ K := by
  rw [← starProjection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜,
    two_smul ℕ, ← two_smul 𝕜]
  refine (smul_right_injective E ?_).eq_iff
  exact two_ne_zero

theorem reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : K.reflection x = x :=
  (reflection_eq_self_iff x).mpr hx

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map_apply {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] (x : E') :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) x = f (K.reflection (f.symm x)) := by
  simp [two_smul, reflection_apply, starProjection_map_apply f K x]

/-- Reflection in the `Submodule.map` of a subspace. -/
theorem reflection_map {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] :
    reflection (K.map (f.toLinearEquiv : E →ₗ[𝕜] E')) = f.symm.trans (K.reflection.trans f) :=
  LinearIsometryEquiv.ext <| reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp]
theorem reflection_bot : reflection (⊥ : Submodule 𝕜 E) = LinearIsometryEquiv.neg 𝕜 := by
  ext; simp [reflection_apply]

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
theorem reflection_mem_subspace_orthogonalComplement_eq_neg {v : E}
    (hv : v ∈ Kᗮ) : K.reflection v = -v := by
  simp [starProjection_apply, reflection_apply,
    orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hv]

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
theorem reflection_mem_subspace_orthogonal_precomplement_eq_neg {v : E}
    (hv : v ∈ K) : Kᗮ.reflection v = -v :=
  reflection_mem_subspace_orthogonalComplement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
theorem reflection_orthogonalComplement_singleton_eq_neg (v : E) : reflection (𝕜 ∙ v)ᗮ v = -v :=
  reflection_mem_subspace_orthogonal_precomplement_eq_neg (Submodule.mem_span_singleton_self v)

theorem reflection_sub {v w : F} (h : ‖v‖ = ‖w‖) : reflection (ℝ ∙ (v - w))ᗮ v = w := by
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ ∙ v - w)ᗮ
  suffices R v + R v = w + w by
    apply smul_right_injective F (by simp : (2 : ℝ) ≠ 0)
    simpa [two_smul] using this
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonalComplement_singleton_eq_neg (v - w)
  have h₂ : R (v + w) = v + w := by
    apply reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [real_inner_add_sub_eq_zero_iff]
    exact h
  convert congr_arg₂ (· + ·) h₂ h₁ using 1
  · simp
  · abel

end reflection

end Submodule

end
