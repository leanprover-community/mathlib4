/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.ContMDiff
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Integral curves of vector fields on a manifold

For any continuously differentiable vector field on a manifold `M` and any chosen non-boundary point
`x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the tangent vector of `γ`
at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.

As a corollary, such an integral curve exists for any starting point `x₀` if `M` is a manifold
without boundary.

## Tags

integral curve, vector field
-/

open scoped Manifold
scoped[Manifold] notation "𝓔(" I ", " x ")" => extChartAt I x
scoped[Manifold] notation "𝓔⁻¹(" I ", " x ")" => LocalEquiv.symm (𝓔(I, x))

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

/-- An interior point of a manifold is a point whose image in the model vector space is in the
interior of the chart's target. -/
def ModelWithCorners.IsInteriorPoint (x : M) := extChartAt I x x ∈ interior (extChartAt I x).target

lemma ModelWithCorners.Boundaryless.isOpen_target
    [I.Boundaryless] {x : M} : IsOpen (extChartAt I x).target := by
rw [extChartAt_target, ModelWithCorners.Boundaryless.range_eq_univ, Set.inter_univ]
exact (ModelWithCorners.continuous_symm _).isOpen_preimage _ (LocalHomeomorph.open_target _)

lemma ModelWithCorners.Boundaryless.isInteriorPoint
    [I.Boundaryless] {x : M} : I.IsInteriorPoint x := by
rw [ModelWithCorners.IsInteriorPoint,
  IsOpen.interior_eq ModelWithCorners.Boundaryless.isOpen_target]
exact LocalEquiv.map_source _ (mem_extChartAt_source _ _)

end

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']
  {v : (x : M) → TangentSpace I x} {x₀ : M}
  (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) (t₀ : ℝ)

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the tangent vector of `γ`
  at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.-/
theorem exists_integralCurve_of_contMDiff_tangent_section (hx : I.IsInteriorPoint x₀) :
    ∃ ε > (0 : ℝ), ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) →
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) := by
rw [contMDiffAt_iff] at hv
obtain ⟨_, hv⟩ := hv
have hI : Set.range I ∈ nhds (extChartAt I x₀ x₀)
· rw [mem_nhds_iff]
  refine ⟨interior (extChartAt I x₀).target,
    subset_trans interior_subset (extChartAt_target_subset_range ..),
    isOpen_interior, hx⟩
obtain ⟨ε1, hε1, f, hf1, hf2⟩ :=
  exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀ (ContDiffAt.snd (hv.contDiffAt hI))
rw [←Real.ball_eq_Ioo] at hf2
-- use continuity of f to extract ε2 so that for t ∈ Real.ball t₀ ε2,
-- f t ∈ interior (extChartAt I x₀).target
have hcont := (hf2 t₀ (Real.ball_eq_Ioo .. ▸ Metric.mem_ball_self hε1)).continuousAt
rw [continuousAt_def, hf1] at hcont
have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀
· apply hcont
  exact IsOpen.mem_nhds isOpen_interior hx
rw [Metric.mem_nhds_iff] at hnhds
obtain ⟨ε2, hε2, hf3⟩ := hnhds
simp_rw [Set.subset_def, Set.mem_preimage] at hf3
-- prove the theorem
refine' ⟨min ε1 ε2, lt_min hε1 hε2, (extChartAt I x₀).symm ∘ f, _, _⟩
· apply Eq.symm
  rw [Function.comp_apply, hf1, LocalEquiv.left_inv _ (mem_extChartAt_source ..)]
intros t ht
rw [←Real.ball_eq_Ioo] at ht
have ht1 := Set.mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left ..))
have ht2 := Set.mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_right ..))
have h : HasDerivAt f
  ((fderivWithin ℝ
        ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
        (Set.range I)
        (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
    (v ((extChartAt I x₀).symm (f t))))
  t := hf2 t ht1
have hf3' := Set.mem_of_mem_of_subset (hf3 t ht2) interior_subset
rw [HasMFDerivAt]
use ContinuousAt.comp
  (continuousAt_extChartAt_symm'' _ _ hf3') ((hf2 t ht1).continuousAt)
apply HasDerivWithinAt.hasFDerivWithinAt
rw [modelWithCornersSelf_coe, Set.range_id, hasDerivWithinAt_univ, ext_chart_model_space_apply,
  writtenInExtChartAt, Function.comp_apply, Function.comp.assoc, extChartAt_model_space_eq_id,
  LocalEquiv.refl_symm, LocalEquiv.refl_coe, Function.comp.right_id, ←Function.comp.assoc]
-- v -> identity v
rw [←tangentBundleCore_coordChange_achart] at h
have hvsub : v ((extChartAt I x₀).symm (f t)) = (tangentBundleCore I M).coordChange
  (achart H x₀) (achart H ((extChartAt I x₀).symm (f t))) ((extChartAt I x₀).symm (f t))
  ((tangentBundleCore I M).coordChange (achart H ((extChartAt I x₀).symm (f t))) (achart H x₀)
    ((extChartAt I x₀).symm (f t)) (v ((extChartAt I x₀).symm (f t))))
· rw [(tangentBundleCore I M).coordChange_comp, (tangentBundleCore I M).coordChange_self]
  · rw [tangentBundleCore_baseSet, coe_achart, ←extChartAt_source I, ←LocalEquiv.symm_target]
    exact mem_extChartAt_source ..
  · rw [tangentBundleCore_baseSet, tangentBundleCore_baseSet, coe_achart, coe_achart,
      ←extChartAt_source I, ←extChartAt_source I, Set.inter_comm, ←Set.inter_assoc, Set.inter_self]
    constructor
    · exact mem_extChartAt_source ..
    · rw [←Set.mem_preimage]
      apply Set.mem_of_mem_of_subset _ (LocalEquiv.source_subset_preimage_target _)
      rw [LocalEquiv.symm_source]
      exact hf3'
rw [hvsub]
apply HasFDerivAt.comp_hasDerivAt _ _ h
rw [tangentBundleCore_coordChange_achart, LocalEquiv.right_inv _ hf3', fderivWithin_of_mem_nhds]
· apply DifferentiableAt.hasFDerivAt
  apply MDifferentiableAt.differentiableAt
  apply MDifferentiableAt.comp (I' := I)
  · exact (contMDiffAt_extChartAt (n := 1)).mdifferentiableAt (le_refl _)
  · apply MDifferentiableOn.mdifferentiableAt
      ((contMDiffOn_extChartAt_symm (n := 1) _).mdifferentiableOn (le_refl _))
    rw [mem_nhds_iff]
    exact ⟨interior (extChartAt I x₀).target, interior_subset, isOpen_interior, hf3 _ ht2⟩
· rw [mem_nhds_iff]
  refine ⟨interior (extChartAt I x₀).target,
    subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hf3 _ ht2⟩

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_integralCurve_of_contMDiff_tangent_section_boundaryless [I.Boundaryless] :
    ∃ ε > (0 : ℝ), ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ ∀ (t : ℝ), t ∈ Set.Ioo (t₀ - ε) (t₀ + ε) →
      HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) :=
  exists_integralCurve_of_contMDiff_tangent_section hv _
    ModelWithCorners.Boundaryless.isInteriorPoint
