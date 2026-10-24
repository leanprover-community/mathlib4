/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Schatten operators

This file defines the Schatten operators, and the required trace, modulus and polar maps in order
to define them.

## Main definitions
 - `ContinuousLinearMap.modulus` the modulus `|T|` for continuous linear maps `T` between Hilbert
   spaces.
 - `ContinuousLinearMap.polarₚₗᵢ` the partial linear isometry `U` such that `T = U† ∘ |T|`.

-/

public noncomputable section

namespace ContinuousLinearMap


open scoped ENNReal InnerProductSpace

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Modulus

/-- The modulus `|T| = √(T†∘T) of a continuous linear map `T : E →L[ℂ] F`. -/
def modulus (T : E →L[ℂ] F) : E →L[ℂ] E := CFC.sqrt (T.adjoint ∘L T)

@[inherit_doc]
scoped notation "|" T "|" => modulus T

@[simp]
theorem modulus_zero : |(0 : E →L[ℂ] F)| = 0 := by simp [modulus]
@[simp]
theorem modulus_neg (T : E →L[ℂ] F) : |-T| = |T| := by simp [modulus]
@[simp]
theorem modulus_nonneg (T : E →L[ℂ] F) : 0 ≤ |T| := by simp [modulus]
@[simp]
theorem modulus_modulus (T : E →L[ℂ] F) : |(|T|)| = |T| := by
  rw [modulus, T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  exact CFC.sqrt_mul_self |T|

theorem modulus_eq_zero (T : E →L[ℂ] F) : |T| = 0 ↔ T = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  simp only [modulus] at h
  rw [CFC.sqrt_eq_zero_iff (adjoint T ∘SL T)
    (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))] at h
  exact adjoint_comp_self_eq_zero_iff.mp h

theorem modulus_comp_modulus (T : E →L[ℂ] F) :
    |T| ∘L |T| = T.adjoint ∘L T := by
  simpa [modulus, ← ContinuousLinearMap.mul_def] using
    CFC.sqrt_mul_sqrt_self (adjoint T ∘L T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T))

theorem norm_modulus_apply (T : E →L[ℂ] F) (x : E) : ‖|T| x‖ = ‖T x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp_rw [apply_norm_sq_eq_inner_adjoint_left, ContinuousLinearMap.comp_apply]
  rw [T.modulus_nonneg.isSelfAdjoint.adjoint_eq]
  simp [modulus, ← mul_apply_eq_comp, CFC.sqrt_mul_sqrt_self (adjoint T ∘SL T)
      (nonneg_iff_isPositive.mpr (ContinuousLinearMap.isPositive_adjoint_comp_self T)),
    ContinuousLinearMap.comp_apply]

theorem ker_modulus_eq (T : E →L[ℂ] F) : |T|.ker = T.ker := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, ← norm_eq_zero (a := T.toLinearMap x),
    ← norm_eq_zero (a := |T|.toLinearMap x)]
  simp [norm_modulus_apply]

end Modulus

section Polar

/-- The polar `U` is a partial linear isometry from the range `|T|.range` of `|T|` to the
orthogonal of the kernel `T.kerᗮ` of the continuous linear map `T : E →L[ℂ] F` such that
`T = U† ∘ |T|`. -/
def polarₚₗᵢ (T : E →L[ℂ] F) : |T|.range.topologicalClosure →ₗᵢ[ℂ] F :=
  LinearMap.extendOfIsometry
    ((Submodule.liftQ _ T (le_of_eq_of_le T.ker_modulus_eq fun ⦃x⦄ a ↦ a))
      ∘ₗ (|T|.quotKerEquivRange).symm.toLinearMap)
    (e := Submodule.inclusion |T|.range.le_topologicalClosure)
    (by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp)
    (by
      rintro ⟨_, x, rfl⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [|T|.quotKerEquivRange_symm_apply_image x]
      simp [norm_modulus_apply])

theorem polarₚₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₚₗᵢ ⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  change T.polarₚₗᵢ (Submodule.inclusion |T|.range.le_topologicalClosure ⟨|T| x, ⟨x, rfl⟩⟩) = _
  simp only [polarₚₗᵢ]
  erw [LinearMap.extendOfIsometry_eq, LinearMap.comp_apply,
    |T|.quotKerEquivRange_symm_apply_image x]
  simp

theorem range_polarₚₗᵢ (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap.range = T.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hd : DenseRange (Submodule.inclusion |T|.range.le_topologicalClosure) := by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp
    refine hd.induction_on m
      (isClosed_closure.preimage T.polarₚₗᵢ.toContinuousLinearMap.continuous) ?_
    rintro ⟨_, x, rfl⟩
    exact subset_closure ⟨x, (T.polarₚₗᵢ_apply x).symm ▸ rfl⟩
  · exact Submodule.topologicalClosure_minimal _
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩, T.polarₚₗᵢ_apply x⟩)
      T.polarₚₗᵢ.isometry.isClosedEmbedding.isClosed_range

theorem polarₚₗᵢ_adjoint_comp (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap.adjoint ∘L T.polarₚₗᵢ.toContinuousLinearMap
     = ContinuousLinearMap.id ℂ _ := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  erw [comp_apply, ContinuousLinearMap.adjoint_inner_left]
  simp [LinearIsometry.inner_map_map T.polarₚₗᵢ x y]

theorem polarₚₗᵢ_comp_adjoint (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap ∘L T.polarₚₗᵢ.toContinuousLinearMap.adjoint
     = T.range.topologicalClosure.starProjection := by
  have : (T.polarₚₗᵢ.toContinuousLinearMap.range).HasOrthogonalProjection := by
    rw [range_polarₚₗᵢ]; infer_instance
  refine ContinuousLinearMap.ext fun x => ?_
  conv_lhs => erw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := T.range.topologicalClosure) x]
  have h0 : T.polarₚₗᵢ.toContinuousLinearMap.adjoint
      ((T.polarₚₗᵢ.toContinuousLinearMap.range : Submodule ℂ F)ᗮ.starProjection x) = 0 :=
    ext_inner_right ℂ fun m => by
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
      simp only [LinearIsometry.toLinearMap_toContinuousLinearMap,
        LinearIsometry.coe_toContinuousLinearMap]
      exact Submodule.inner_left_of_mem_orthogonal (K := T.polarₚₗᵢ.range) ⟨m, rfl⟩
        (Submodule.starProjection_apply_mem (T.polarₚₗᵢ.range)ᗮ x)
  simp only [← T.range_polarₚₗᵢ, LinearIsometry.toLinearMap_toContinuousLinearMap, map_add,
    comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  erw [h0, map_zero, add_zero]
  obtain ⟨m, hm⟩ := Submodule.starProjection_apply_mem
    (T.polarₚₗᵢ.toContinuousLinearMap.range : Submodule ℂ F) x
  erw [← hm, LinearIsometry.toLinearMap_toContinuousLinearMap, LinearIsometry.coe_toLinearMap,
    LinearIsometry.map_eq_iff, ← comp_apply, T.polarₚₗᵢ_adjoint_comp]
  simp

end Polar

end ContinuousLinearMap
