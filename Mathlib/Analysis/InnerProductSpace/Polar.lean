/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Abs
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Polar decomposition

This file defines the polar decomposition for a continuous linear map `T : E →L[ℂ] F`
between (potentially distinct) Hilbert spaces `E` and `F`.

## Main definitions
 - `ContinuousLinearMap.polarₗᵢ` the partial linear isometry `U` such that `T = U ∘ |T|`.

-/

public noncomputable section

namespace ContinuousLinearMap


open scoped ENNReal InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Polar

@[inherit_doc]
local notation "|" T "|" => abs T

/-- The polar `U` is a partial linear isometry from the range `|T|.range` of `|T|` to the
orthogonal of the kernel `T.kerᗮ` of the continuous linear map `T : E →L[ℂ] F` such that
`T = U ∘ |T|`. -/
def polarₗᵢ (T : E →L[ℂ] F) : |T|.range.topologicalClosure →ₗᵢ[ℂ] F :=
  LinearMap.extendOfIsometry
    ((Submodule.liftQ _ T (le_of_eq_of_le T.ker_abs_eq fun ⦃x⦄ a ↦ a))
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
      simp [norm_abs_apply])

theorem polarₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₗᵢ ⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  change T.polarₗᵢ (Submodule.inclusion |T|.range.le_topologicalClosure ⟨|T| x, ⟨x, rfl⟩⟩) = _
  simp only [polarₗᵢ]
  erw [LinearMap.extendOfIsometry_eq, LinearMap.comp_apply,
    |T|.quotKerEquivRange_symm_apply_image x]
  simp

theorem range_polarₗᵢ (T : E →L[ℂ] F) :
    T.polarₗᵢ.toContinuousLinearMap.range = T.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hd : DenseRange (Submodule.inclusion |T|.range.le_topologicalClosure) := by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
      simp
    refine hd.induction_on m
      (isClosed_closure.preimage T.polarₗᵢ.toContinuousLinearMap.continuous) ?_
    rintro ⟨_, x, rfl⟩
    exact subset_closure ⟨x, (T.polarₗᵢ_apply x).symm ▸ rfl⟩
  · exact Submodule.topologicalClosure_minimal _
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩, T.polarₗᵢ_apply x⟩)
      T.polarₗᵢ.isometry.isClosedEmbedding.isClosed_range

theorem polarₗᵢ_adjoint_comp (T : E →L[ℂ] F) :
    T.polarₗᵢ.toContinuousLinearMap.adjoint ∘L T.polarₗᵢ.toContinuousLinearMap
     = ContinuousLinearMap.id ℂ _ := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  erw [comp_apply, ContinuousLinearMap.adjoint_inner_left]
  simp [LinearIsometry.inner_map_map T.polarₗᵢ x y]

theorem polarₗᵢ_comp_adjoint (T : E →L[ℂ] F) :
    T.polarₗᵢ.toContinuousLinearMap ∘L T.polarₗᵢ.toContinuousLinearMap.adjoint
     = T.range.topologicalClosure.starProjection := by
  have : (T.polarₗᵢ.toContinuousLinearMap.range).HasOrthogonalProjection := by
    rw [range_polarₗᵢ]; infer_instance
  refine ContinuousLinearMap.ext fun x => ?_
  conv_lhs => erw [← Submodule.starProjection_add_starProjection_orthogonal
    (K := T.range.topologicalClosure) x]
  have h0 : T.polarₗᵢ.toContinuousLinearMap.adjoint
      ((T.polarₗᵢ.toContinuousLinearMap.range : Submodule ℂ F)ᗮ.starProjection x) = 0 :=
    ext_inner_right ℂ fun m => by
      rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
      simp only [LinearIsometry.toLinearMap_toContinuousLinearMap,
        LinearIsometry.coe_toContinuousLinearMap]
      exact Submodule.inner_left_of_mem_orthogonal (K := T.polarₗᵢ.range) ⟨m, rfl⟩
        (Submodule.starProjection_apply_mem (T.polarₗᵢ.range)ᗮ x)
  simp only [← T.range_polarₗᵢ, LinearIsometry.toLinearMap_toContinuousLinearMap, map_add,
    comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  erw [h0, map_zero, add_zero]
  obtain ⟨m, hm⟩ := Submodule.starProjection_apply_mem
    (T.polarₗᵢ.toContinuousLinearMap.range : Submodule ℂ F) x
  erw [← hm, LinearIsometry.toLinearMap_toContinuousLinearMap, LinearIsometry.coe_toLinearMap,
    LinearIsometry.map_eq_iff, ← comp_apply, T.polarₗᵢ_adjoint_comp]
  simp

end Polar

end ContinuousLinearMap
