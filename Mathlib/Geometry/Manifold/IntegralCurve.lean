/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Integral curves of vector fields on a manifold

For any continuously differentiable vector field on a manifold `M` and any chosen interior point
`x₀ : M`, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector of
`γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around `t₀`.

As a corollary, such an integral curve exists for any starting point `x₀` if `M` is a manifold
without boundary.

## Main definition

- **IsIntegralCurve γ v t₀ x₀**: If `v : M → TM` is a vector field on `M` and `x : M`,
`IsIntegralCurveAt γ v t₀ x₀` means `γ : ℝ → M` is a differentiable integral curve of `v` with
`γ x₀ = t₀`.

## Tags

integral curve, vector field, local existence
-/

open scoped Manifold
open Set

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']

variable (I) in
def tangentCoordChange (x y : M) := (tangentBundleCore I M).coordChange (achart H x) (achart H y)

lemma tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl

lemma tangentCoordChange_self {x z : M} {v : E} (h : z ∈ (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart, ←extChartAt_source I]
  exact h

-- continuousOn?

lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z ∈ (extChartAt I w).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ←extChartAt_source I]
  exact h

lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : extChartAt I x z ∈ ((extChartAt I x).symm ≫ (extChartAt I y)).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  ((contDiffWithinAt_ext_coord_change I y x h).differentiableWithinAt (by simp)).hasFDerivWithinAt

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

/-- If `v : M → TM` is a vector field on `M` and `x : M`, `IsIntegralCurveAt γ v t₀ x₀` means
  `γ : ℝ → M` is a differentiable integral curve of `v` with `γ x₀ = t₀`. -/
def IsIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) (x₀ : M) :=
  γ t₀ = x₀ ∧ ∃ ε > (0 : ℝ), ∀ (t : ℝ), t ∈ Ioo (t₀ - ε) (t₀ + ε) →
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

/-
TODO:
* split the theorem below into smaller lemmas, e.g. involving IsIntegralCurveAt?
* shift and stretch theorems
* constant curve at stationary point of v
-/
variable {t₀}

lemma IsIntegralCurveAt.comp_add {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (fun t => t + dt)) v (t₀ - dt) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine' ⟨by simp [h1], ε, hε, _⟩
  intros t ht
  rw [sub_right_comm, sub_add_eq_add_sub, ←add_mem_Ioo_iff_left] at ht
  have h2' := h2 (t + dt) ht
  rw [Function.comp_apply,
    ←ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivAt.comp t h2'
  /- this makes me think we need lemmas for `HasMFDerivAt 𝓘(E, E) 𝓘(E, E)` of simple operations -/
  refine' ⟨(continuous_add_right _).continuousAt, _⟩
  simp only [writtenInExtChartAt, extChartAt, LocalHomeomorph.extend,
    LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_source,
    LocalHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_localEquiv,
    LocalEquiv.trans_refl, LocalEquiv.refl_coe, LocalEquiv.refl_symm, Function.comp.right_id,
    Function.comp.left_id, modelWithCornersSelf_coe, range_id, id_eq, hasFDerivWithinAt_univ]
  apply HasFDerivAt.add_const
  exact hasFDerivAt_id _

lemma isIntegralCurveAt_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurveAt γ v t₀ x₀ ↔
    IsIntegralCurveAt (γ ∘ (fun t => t + dt)) v (t₀ - dt) x₀ := by
  refine' ⟨fun hγ => IsIntegralCurveAt.comp_add hγ _, _⟩
  intro hγ
  have := hγ.comp_add (-dt)
  rw [sub_neg_eq_add, sub_add_cancel] at this
  convert this
  ext
  simp

lemma IsIntegralCurveAt.comp_mul_pos {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) {a : ℝ}
    (ha : 0 < a) : IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine' ⟨by rw [Function.comp_apply, div_mul_cancel _ (ne_of_gt ha)]; exact h1, ε / a,
    div_pos hε ha, _⟩
  intros t ht
  have ht : t * a ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    rw [mem_Ioo, ←div_lt_iff ha, ←lt_div_iff ha, sub_div, add_div]
    exact ht
  have h2' := h2 (t * a) ht
  rw [Function.comp_apply, Pi.smul_apply, ←ContinuousLinearMap.smulRight_comp]
  apply HasMFDerivAt.comp t h2'
  refine' ⟨(continuous_mul_right _).continuousAt, _⟩
  simp only [writtenInExtChartAt, extChartAt, LocalHomeomorph.extend,
    LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_source,
    LocalHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_localEquiv,
    LocalEquiv.trans_refl, LocalEquiv.refl_coe, LocalEquiv.refl_symm, Function.comp.right_id,
    Function.comp.left_id, modelWithCornersSelf_coe, range_id, id_eq, hasFDerivWithinAt_univ]
  apply HasFDerivAt.mul_const'
  exact hasFDerivAt_id _

lemma isIntegralCurvAt_comp_mul_pos {γ : ℝ → M} {a : ℝ} (ha : 0 < a) :
    IsIntegralCurveAt γ v t₀ x₀ ↔ IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  refine' ⟨fun hγ => IsIntegralCurveAt.comp_mul_pos hγ ha, _⟩
  intro hγ
  have := hγ.comp_mul_pos (inv_pos_of_pos ha)
  rw [smul_smul, inv_mul_eq_div, div_self (ne_of_gt ha), one_smul, ←div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self (ne_of_gt ha), div_one, Function.comp.assoc] at this
  convert this
  ext
  simp [inv_mul_eq_div, div_self (ne_of_gt ha)]

lemma IsIntegralCurveAt.comp_neg {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) :
    IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine' ⟨by simp [h1], ε, hε, _⟩
  intros t ht
  rw [←neg_add', neg_add_eq_sub, ←neg_sub, ←neg_mem_Ioo_iff] at ht
  have h2' := h2 (-t) ht
  rw [Function.comp_apply, Pi.neg_apply, ←neg_one_smul ℝ (v (γ (-t))),
    ←ContinuousLinearMap.smulRight_comp]
  apply HasMFDerivAt.comp t h2'
  refine' ⟨continuousAt_neg, _⟩
  simp only [writtenInExtChartAt, extChartAt, LocalHomeomorph.extend,
    LocalHomeomorph.refl_localEquiv, LocalEquiv.refl_source,
    LocalHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_localEquiv,
    LocalEquiv.trans_refl, LocalEquiv.refl_coe, LocalEquiv.refl_symm, Function.comp.right_id,
    Function.comp.left_id, modelWithCornersSelf_coe, range_id, id_eq, hasFDerivWithinAt_univ]
  apply HasDerivAt.hasFDerivAt
  exact hasDerivAt_neg _

lemma isIntegralCurveAt_comp_neg {γ : ℝ → M} :
    IsIntegralCurveAt γ v t₀ x₀ ↔ IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) x₀ := by
  refine' ⟨fun hγ => IsIntegralCurveAt.comp_neg hγ, _⟩
  intro hγ
  have := hγ.comp_neg
  rw [Function.comp.assoc, neg_comp_neg, neg_neg, neg_neg] at this
  exact this

lemma IsIntegralCurveAt.comp_mul_ne_zero {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) {a : ℝ}
    (ha : a ≠ 0) : IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  rw [ne_iff_lt_or_gt] at ha
  cases' ha with ha ha
  · apply isIntegralCurveAt_comp_neg.mpr
    have : (fun t ↦ t * a) ∘ Neg.neg = fun t ↦ t * -a := by ext; simp
    rw [Function.comp.assoc, this, ←neg_smul, ←div_neg]
    exact hγ.comp_mul_pos (neg_pos_of_neg ha)
  · exact hγ.comp_mul_pos ha

lemma isIntegralCurveAt_comp_mul_ne_zero {γ : ℝ → M} {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt γ v t₀ x₀ ↔ IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  refine' ⟨fun hγ => IsIntegralCurveAt.comp_mul_ne_zero hγ ha, _⟩
  intro hγ
  have := hγ.comp_mul_ne_zero (inv_ne_zero ha)
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, ←div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self ha, div_one, Function.comp.assoc] at this
  convert this
  ext
  simp [inv_mul_eq_div, div_self ha]

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector
  of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around
  `t₀`.-/
theorem exists_integralCurve_of_contMDiff_tangent_section (hx : I.IsInteriorPoint x₀) :
    ∃ (γ : ℝ → M), IsIntegralCurveAt γ v t₀ x₀ := by
  /- express the derivative of the section `v` in the local charts -/
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  /- use Picard-Lindelöf theorem to extract a solution to the ODE in the chart defined by `v` -/
  obtain ⟨f, hf1, ε1, hε1, hf2⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀
      (ContDiffAt.snd (hv.contDiffAt (SmoothManifoldWithCorners.range_mem_nhds_isInteriorPoint hx)))
  rw [←Real.ball_eq_Ioo] at hf2
  /- use continuity of `f` to extract `ε2` so that for `t ∈ Real.ball t₀ ε2`,
    `f t ∈ interior (extChartAt I x₀).target` -/
  have hcont := (hf2 t₀ (Real.ball_eq_Ioo .. ▸ Metric.mem_ball_self hε1)).continuousAt
  rw [continuousAt_def, hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀ :=
    hcont _ (IsOpen.mem_nhds isOpen_interior hx)
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ε2, hε2, hf3⟩ := hnhds
  simp_rw [subset_def, mem_preimage] at hf3
  /- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve -/
  refine' ⟨(extChartAt I x₀).symm ∘ f, _, min ε1 ε2, lt_min hε1 hε2, _⟩
  · apply Eq.symm
    rw [Function.comp_apply, hf1, LocalEquiv.left_inv _ (mem_extChartAt_source ..)]
  intros t ht
  /- collect useful terms in convenient forms -/
  rw [←Real.ball_eq_Ioo] at ht
  have ht1 := mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left ..))
  have ht2 := mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_right ..))
  have h : HasDerivAt f
    ((fderivWithin ℝ ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
        (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
      (v ((extChartAt I x₀).symm (f t))))
    t := hf2 t ht1
  rw [←tangentCoordChange_def] at h
  have hf3' := mem_of_mem_of_subset (hf3 t ht2) interior_subset
  /- express the derivative of the integral curve in the local chart -/
  rw [HasMFDerivAt]
  use ContinuousAt.comp
    (continuousAt_extChartAt_symm'' _ _ hf3') ((hf2 t ht1).continuousAt)
  apply HasDerivWithinAt.hasFDerivWithinAt
  rw [modelWithCornersSelf_coe, range_id, hasDerivWithinAt_univ, ext_chart_model_space_apply,
    writtenInExtChartAt, Function.comp_apply, Function.comp.assoc, extChartAt_model_space_eq_id,
    LocalEquiv.refl_symm, LocalEquiv.refl_coe, Function.comp.right_id, ←Function.comp.assoc]
  /- `h` gives the derivative of `f` at `t` as `↑D (v (γ t))`, where `D` is the change of
    coordinates from the chart at `γ t` to the chart at `x₀`. we wish to use
    `HasFDerivAt.comp_hasDerivAt` to get the derivative of `γ` at `t` as `v (γ t)`, which requires
    first expressing `v (γ t)` as `↑D_inv ↑D (v (γ t))`, where `D_inv` is the opposite change of
    coordinates as `D`. -/
  rw [←tangentCoordChange_self (I := I) (M := M) (x := (extChartAt I x₀).symm (f t))
    (z := (extChartAt I x₀).symm (f t)) (v := v ((extChartAt I x₀).symm (f t)))]
  rw [←tangentCoordChange_comp (x := x₀)]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I)
  nth_rw 4 [←(extChartAt I x₀).right_inv hf3']
  apply hasFDerivWithinAt_tangentCoordChange
  · rw [LocalEquiv.right_inv _ hf3', LocalEquiv.trans_source, LocalEquiv.symm_source]
    use hf3'
    rw [mem_preimage]
    exact mem_extChartAt_source ..
  · rw [mem_nhds_iff]
    exact ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..), isOpen_interior, hf3 _ ht2⟩
  · rw [inter_right_comm, inter_self, mem_inter_iff]
    use mem_extChartAt_source ..
    rw [←mem_preimage]
    exact mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  · exact mem_extChartAt_source ..

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_integralCurve_of_contMDiff_tangent_section_boundaryless [I.Boundaryless] :
    ∃ (γ : ℝ → M), IsIntegralCurveAt γ v t₀ x₀ :=
  exists_integralCurve_of_contMDiff_tangent_section hv I.isInteriorPoint
