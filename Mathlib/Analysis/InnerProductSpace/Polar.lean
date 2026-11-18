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
 - `ContinuousLinearMap.polarₚₗᵢ` the linear isometry `U : T.abs.range → T.kerᗮ` such that
   `T = U ∘ T.abs`.
 - `ContinuousLinearMap.polar` the partial linear isometry `U : E →L[ℂ] F` for a continuous
   linear map `T : E →L[ℂ] F` gotten by extending the map `ContinuousLinearMap.polarₚₗᵢ` by zero.

-/

public noncomputable section

namespace ContinuousLinearMap


open scoped ENNReal InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Polar

/-- The polar `U` is a linear isometry from the range `T.abs.range` of `T.abs` to the
orthogonal of the kernel `T.kerᗮ` of the continuous linear map `T : E →L[ℂ] F` such that
`T = U ∘ T.abs`. -/
def polarₚₗᵢ (T : E →L[ℂ] F) : T.abs.range.topologicalClosure →ₗᵢ[ℂ] F :=
  LinearMap.extendOfIsometry
    ((Submodule.liftQ _ T (le_of_eq_of_le T.ker_abs fun ⦃x⦄ a ↦ a))
      ∘ₗ (T.abs.quotKerEquivRange).symm.toLinearMap)
    (e := Submodule.inclusion T.abs.range.le_topologicalClosure)
    (by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using T.abs.range.le_topologicalClosure)]
      simp)
    (by
      rintro ⟨_, x, rfl⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      erw [T.abs.quotKerEquivRange_symm_apply_image x]
      simp [norm_abs_apply])

theorem polarₚₗᵢ_apply (T : E →L[ℂ] F) (x : E) :
    T.polarₚₗᵢ ⟨T.abs x, T.abs.range.le_topologicalClosure ⟨x, rfl⟩⟩ = T x := by
  change T.polarₚₗᵢ (Submodule.inclusion T.abs.range.le_topologicalClosure ⟨T.abs x, ⟨x, rfl⟩⟩) = _
  simp only [polarₚₗᵢ]
  erw [LinearMap.extendOfIsometry_eq, LinearMap.comp_apply,
    T.abs.quotKerEquivRange_symm_apply_image x]
  simp

theorem range_polarₚₗᵢ (T : E →L[ℂ] F) :
    T.polarₚₗᵢ.toContinuousLinearMap.range = T.range.topologicalClosure := by
  apply le_antisymm
  · rintro _ ⟨m, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hd : DenseRange (Submodule.inclusion T.abs.range.le_topologicalClosure) := by
      erw [denseRange_inclusion_iff (by
        simpa [← SetLike.coe_subset_coe] using T.abs.range.le_topologicalClosure)]
      simp
    refine hd.induction_on m
      (isClosed_closure.preimage T.polarₚₗᵢ.toContinuousLinearMap.continuous) ?_
    rintro ⟨_, x, rfl⟩
    exact subset_closure ⟨x, (T.polarₚₗᵢ_apply x).symm ▸ rfl⟩
  · exact Submodule.topologicalClosure_minimal _
      (by
        rintro _ ⟨x, rfl⟩
        exact ⟨⟨T.abs x, T.abs.range.le_topologicalClosure ⟨x, rfl⟩⟩, T.polarₚₗᵢ_apply x⟩)
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

/-- The polar `U : E →L[ℂ] F` is a partial linear isometry of the continuous linear map
`T : E →L[ℂ] F` such  that `T = U ∘ T.abs`, linearly isometric from the range `T.abs.range` of
`T.abs` to the orthogonal of the kernel `T.kerᗮ` of `T` and extended by zero from `T.abs.range`
to `E`. -/
def polar (T : E →L[ℂ] F) : E →L[ℂ] F :=
  T.polarₚₗᵢ.toContinuousLinearMap ∘L T.abs.range.topologicalClosure.orthogonalProjectionOnto

theorem apply_eq_zero_tfae (T : E →L[ℂ] F) (x : E) :
    List.TFAE [T x = 0, T.polar x = 0, T.abs x = 0] := by
  tfae_have 1 ↔ 3 := by
    rw [← norm_eq_zero (a := T x), ← norm_eq_zero (a := T.abs x), norm_abs_apply]
  have hT : T.polar x = 0 ↔ (∀ u ∈ T.abs.range, ⟪u, x⟫_ℂ = 0) := by
    rw [polar, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    map_eq_zero_iff _ T.polarₚₗᵢ.injective,
    Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_closure,
    Submodule.mem_orthogonal]
  tfae_have 2 → 3 := by
    rw [hT]
    intro h
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← ContinuousLinearMap.adjoint_inner_left, T.isSelfAdjoint_abs.adjoint_eq]
    exact h (T.abs (T.abs x)) ⟨T.abs x, rfl⟩
  tfae_have 3 → 2 := by
    rw [hT]
    rintro h _ ⟨y, rfl⟩
    rw [← T.isSelfAdjoint_abs.adjoint_eq]
    simp [← ContinuousLinearMap.adjoint_inner_right, h]
  tfae_finish

theorem polar_eq_zero_iff (T : E →L[ℂ] F) (x : E) : T.polar x = 0 ↔ T x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 2 1)

theorem abs_eq_zero_iff (T : E →L[ℂ] F) (x : E) : T.abs x = 0 ↔ T x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 3 1)

theorem polar_eq_zero_iff_abs_eq_zero (T : E →L[ℂ] F) (x : E) :
    T.polar x = 0 ↔ T.abs x = 0 := by
  exact ((T.apply_eq_zero_tfae x).out 2 3)

theorem ker_polar_eq (T : E →L[ℂ] F) : T.polar.ker = T.ker := by
  ext x
  simp [LinearMap.mem_ker, T.polar_eq_zero_iff]

theorem polar_comp_polar_adjoint_eq_starProjection (T : E →L[ℂ] F) :
    T.polar ∘L T.polar.adjoint = T.range.topologicalClosure.starProjection := by
  have h : T.abs.range.topologicalClosure.orthogonalProjectionOnto
      ∘L T.abs.range.topologicalClosure.subtypeL = ContinuousLinearMap.id ℂ _ := by
    ext x; simp
  unfold polar
  simp_rw +singlePass [adjoint_comp, comp_assoc, Submodule.adjoint_orthogonalProjectionOnto]
  rw [← comp_assoc T.abs.range.topologicalClosure.orthogonalProjectionOnto, h]
  simp [polarₚₗᵢ_comp_adjoint]

theorem polar_adjoint_comp_polar_eq_starProjection (T : E →L[ℂ] F) :
    T.polar.adjoint ∘L T.polar = T.abs.range.topologicalClosure.starProjection := by
  unfold polar
  simp_rw +singlePass [adjoint_comp, comp_assoc,
    ← comp_assoc T.polarₚₗᵢ.toContinuousLinearMap.adjoint]
  simp [Submodule.adjoint_orthogonalProjectionOnto, one_def, id_comp]
  rfl

theorem polar_comp_abs (T : E →L[ℂ] F) : T.polar ∘L T.abs = T := by
  ext x
  simp only [polar, ContinuousLinearMap.comp_apply]
  nth_rw 4 [← polarₚₗᵢ_apply]
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.map_eq_iff]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨T.abs x, T.abs.range.le_topologicalClosure (by simp)⟩

theorem polar_adjoint_comp_self_eq_abs (T : E →L[ℂ] F) : T.polar.adjoint ∘L T = T.abs := by
  nth_rw 2 [← T.polar_comp_abs]
  erw [← comp_assoc, T.polar_adjoint_comp_polar_eq_starProjection]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  exact Submodule.starProjection_eq_self_iff.mpr (T.abs.range.le_topologicalClosure ⟨x, rfl⟩)

theorem polar_unique {T : E →L[ℂ] F} {W : E →L[ℂ] F} (h : W ∘L T.abs = T)
    (hker : W.ker = T.ker) : W = T.polar := by
  ext x
  erw [← Submodule.starProjection_add_starProjection_orthogonal (K := T.ker) x, map_add, map_add]
  refine congr_arg₂ _ ?_ ?_
  · refine (fun z hz => ?_ : ∀ z ∈ T.ker, W z = T.polar z) _
      (Submodule.starProjection_apply_mem T.ker x)
    have hWz : z ∈ W.ker := hker ▸ hz
    have hTz : z ∈ T.polar.ker := T.ker_polar_eq ▸ hz
    erw [LinearMap.mem_ker.mp hTz, LinearMap.mem_ker.mp hWz]
  · refine (fun z hz => ?_ : ∀ z ∈ T.kerᗮ, W z = T.polar z) _ (T.kerᗮ.starProjection_apply_mem x)
    refine Set.EqOn.closure (s := (T.abs.range : Set E))
      (by
        rintro _ ⟨y, rfl⟩
        exact (DFunLike.congr_fun h y).trans (DFunLike.congr_fun T.polar_comp_abs y).symm
      )
      W.continuous
      T.polar.continuous
      ?_
    rw [← Submodule.topologicalClosure_coe, ← Submodule.orthogonal_orthogonal_eq_closure]
    refine Submodule.orthogonal_le (fun w hw => ?_) hz
    erw [LinearMap.mem_ker, ← norm_eq_zero, ← norm_abs_apply]
    refine norm_eq_zero.mpr ((inner_self_eq_zero (𝕜 := ℂ) (x := T.abs w)).mp ?_)
    rw [← ContinuousLinearMap.adjoint_inner_left, T.isSelfAdjoint_abs.adjoint_eq]
    exact (Submodule.mem_orthogonal _ _).mp hw _ ⟨T.abs w, rfl⟩

theorem abs_adjoint (T : E →L[ℂ] F) :
    T.adjoint.abs = T.polar ∘L T.abs ∘L T.polar.adjoint := by
  have h : (T.polar ∘L T.abs ∘L T.polar.adjoint) ∘L
      (T.polar ∘L T.abs ∘L T.polar.adjoint) = T ∘L T.adjoint := by
    calc
      (T.polar ∘L T.abs ∘L T.polar.adjoint) ∘L (T.polar ∘L T.abs ∘L T.polar.adjoint)
        = T.polar ∘L T.abs ∘L
            ((T.polar.adjoint ∘L T.polar ∘L T.abs) ∘L T.polar.adjoint) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = T.polar ∘L T.abs ∘L (T.abs ∘L T.polar.adjoint) := by
          erw [T.polar_comp_abs, T.polar_adjoint_comp_self_eq_abs]
      _ = (T.polar ∘L T.abs) ∘L (T.polar ∘L T.abs).adjoint := by
          simp only [ContinuousLinearMap.adjoint_comp, T.isSelfAdjoint_abs.adjoint_eq,
            ContinuousLinearMap.comp_assoc]
      _ = T ∘L T.adjoint := by rw [T.polar_comp_abs]
  rw [T.adjoint.abs_def, ContinuousLinearMap.adjoint_adjoint, ← h]
  exact CFC.sqrt_mul_self _
    (nonneg_iff_isPositive.mpr (T.isPositive_abs.conj_adjoint T.polar))

theorem adjoint_polar (T : E →L[ℂ] F) : T.adjoint.polar = T.polar.adjoint := by
  apply Eq.symm
  apply polar_unique (T := T.adjoint)
  · erw [T.abs_adjoint]
    calc
      T.polar.adjoint ∘L T.polar ∘L T.abs ∘L T.polar.adjoint =
          (T.polar.adjoint ∘L (T.polar ∘L T.abs)) ∘L T.polar.adjoint := by
        simp only [comp_assoc]
      _ = T.abs ∘L T.polar.adjoint := by
        rw [T.polar_comp_abs, T.polar_adjoint_comp_self_eq_abs]
      _ = T.adjoint := by
        nth_rw 3 [← T.polar_comp_abs]
        simp [adjoint_comp, T.isSelfAdjoint_abs.adjoint_eq]
  · ext x
    simp_rw [LinearMap.mem_ker]
    constructor
    · rintro hx
      refine ext_inner_right ℂ (fun y => ?_)
      rw [← T.polar_comp_abs]
      simp only [adjoint_comp, toLinearMap_comp, LinearMap.coe_comp, coe_coe, Function.comp_apply,
        inner_zero_left, ContinuousLinearMap.adjoint_inner_left]
      erw [← ContinuousLinearMap.adjoint_inner_left, hx, inner_zero_left]
    · rintro hx
      have h := congrArg (fun A => A x) T.polar_comp_polar_adjoint_eq_starProjection
      simp only [ContinuousLinearMap.comp_apply] at h
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      erw [ContinuousLinearMap.adjoint_inner_left, h, inner_eq_zero_symm]
      refine Submodule.inner_right_of_mem_orthogonal
        (Submodule.starProjection_apply_mem _ x) ?_
      rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
      rintro _ ⟨y, rfl⟩
      erw [← ContinuousLinearMap.adjoint_inner_right, hx, inner_zero_right]

theorem norm_polar_le_one (T : E →L[ℂ] F) : ‖T.polar‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, polar, ContinuousLinearMap.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact Submodule.norm_orthogonalProjectionOnto_apply_le _ x

end Polar

end ContinuousLinearMap
