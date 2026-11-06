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
 - `ContinuousLinearMap.polarₗᵢ` the linear isometry `U : |T|.range.topologicalClosure →ₗᵢ[ℂ] F`
    such that `T = U ∘ |T|`.

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

private def polarₗᵢAux (T : E →L[ℂ] F) : |T|.range →ₗ[ℂ] F :=
  Submodule.liftQ _ T (le_of_eq_of_le T.ker_abs_eq fun ⦃x⦄ a ↦ a)
    ∘ₗ (|T|.quotKerEquivRange).symm.toLinearMap

@[simp]
private theorem polarₗᵢAux_apply (T : E →L[ℂ] F) (x : E) (h : |T| x ∈ |T|.range) :
    polarₗᵢAux T ⟨|T| x, h⟩ = T x := by
  exact congrArg _ (|T|.quotKerEquivRange_symm_apply_image x h)

private theorem denseRange_inclusion (T : E →L[ℂ] F) :
    DenseRange (Submodule.inclusion |T|.range.le_topologicalClosure) := by
  erw [denseRange_inclusion_iff (by
    simpa [← SetLike.coe_subset_coe] using |T|.range.le_topologicalClosure)]
  simp

/-- The polar `U` is a linear isometry from the range `|T|.range` of `|T|` to the orthogonal of
the kernel `T.kerᗮ` of the continuous linear map `T : E →L[ℂ] F` such that `T = U ∘ |T|`. -/
def polarₗᵢ (T : E →L[ℂ] F) : |T|.range.topologicalClosure →ₗᵢ[ℂ] F :=
  T.polarₗᵢAux.extendOfIsometry
    (e := Submodule.inclusion |T|.range.le_topologicalClosure)
    T.denseRange_inclusion
    (by
      rintro ⟨_, x, rfl⟩
      simp [norm_abs_apply])

theorem polarₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₗᵢ ⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  rw [← Submodule.inclusion_apply |T|.range.le_topologicalClosure
    ⟨|T| x, LinearMap.mem_range_self _ x⟩]
  simp [polarₗᵢ]

theorem range_polarₗᵢ (T : E →L[ℂ] F) :
    T.polarₗᵢ.range = T.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine T.denseRange_inclusion.induction_on m
      (isClosed_closure.preimage T.polarₗᵢ.toContinuousLinearMap.continuous) ?_
    rintro ⟨_, x, rfl⟩
    exact subset_closure ⟨x, (T.polarₗᵢ_apply x).symm ▸ rfl⟩
  · exact Submodule.topologicalClosure_minimal _
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨|T| x, |T|.range.le_topologicalClosure ⟨x, rfl⟩⟩, T.polarₗᵢ_apply x⟩)
      T.polarₗᵢ.isometry.isClosedEmbedding.isClosed_range

theorem polarₗᵢ_adjoint_comp (T : E →L[ℂ] F) :
    T.polarₗᵢ.toContinuousLinearMap.adjoint ∘L T.polarₗᵢ.toContinuousLinearMap = .id ℂ _ := by
  refine ContinuousLinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  simp

theorem polarₗᵢ_comp_adjoint (T : E →L[ℂ] F) :
    T.polarₗᵢ.toContinuousLinearMap ∘L T.polarₗᵢ.toContinuousLinearMap.adjoint
     = T.range.topologicalClosure.starProjection := by
  ext
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun _ hy ↦ ?_).symm
  · simp_rw [← range_polarₗᵢ]
    simp
  · simp_rw [← range_polarₗᵢ] at hy
    obtain ⟨_, rfl⟩ := hy
    simp [inner_sub_left, adjoint_inner_left]

end Polar

end ContinuousLinearMap
