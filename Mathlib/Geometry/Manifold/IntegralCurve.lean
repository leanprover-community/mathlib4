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

variable {t₀}

lemma IsIntegralCurveAt.comp_add {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (fun t => t + dt)) v (t₀ - dt) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine ⟨by simp [h1], ε, hε, ?_⟩
  intros t ht
  rw [sub_right_comm, sub_add_eq_add_sub, ←add_mem_Ioo_iff_left] at ht
  have h2' := h2 (t + dt) ht
  rw [Function.comp_apply,
    ←ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivAt.comp t h2'
  /- this makes me think we need lemmas for `HasMFDerivAt 𝓘(E, E) 𝓘(E, E)` of simple operations -/
  refine ⟨(continuous_add_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  apply HasFDerivAt.add_const (hasFDerivAt_id _)

lemma isIntegralCurveAt_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurveAt γ v t₀ x₀ ↔
    IsIntegralCurveAt (γ ∘ (fun t => t + dt)) v (t₀ - dt) x₀ := by
  refine ⟨fun hγ => IsIntegralCurveAt.comp_add hγ _, fun hγ ↦ ?_⟩
  have := hγ.comp_add (-dt)
  rw [sub_neg_eq_add, sub_add_cancel] at this
  convert this
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma IsIntegralCurveAt.comp_mul_pos {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) {a : ℝ}
    (ha : 0 < a) : IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine ⟨by rw [Function.comp_apply, div_mul_cancel _ (ne_of_gt ha)]; exact h1, ε / a,
    div_pos hε ha, ?_⟩
  intros t ht
  have ht : t * a ∈ Ioo (t₀ - ε) (t₀ + ε) := by
    rw [mem_Ioo, ←div_lt_iff ha, ←lt_div_iff ha, sub_div, add_div]
    exact ht
  rw [Function.comp_apply, Pi.smul_apply, ←ContinuousLinearMap.smulRight_comp]
  refine HasMFDerivAt.comp t (h2 (t * a) ht) ⟨(continuous_mul_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  apply HasFDerivAt.mul_const' (hasFDerivAt_id _)

lemma isIntegralCurvAt_comp_mul_pos {γ : ℝ → M} {a : ℝ} (ha : 0 < a) :
    IsIntegralCurveAt γ v t₀ x₀ ↔ IsIntegralCurveAt (γ ∘ (fun t => t * a)) (a • v) (t₀ / a) x₀ := by
  refine ⟨fun hγ => IsIntegralCurveAt.comp_mul_pos hγ ha, fun hγ ↦ ?_⟩
  have := hγ.comp_mul_pos (inv_pos_of_pos ha)
  rw [smul_smul, inv_mul_eq_div, div_self (ne_of_gt ha), one_smul, ←div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self (ne_of_gt ha), div_one, Function.comp.assoc] at this
  convert this
  ext
  simp [inv_mul_eq_div, div_self (ne_of_gt ha)]

lemma IsIntegralCurveAt.comp_neg {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀ x₀) :
    IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) x₀ := by
  obtain ⟨h1, ε, hε, h2⟩ := hγ
  refine ⟨by simp [h1], ε, hε, ?_⟩
  intros t ht
  rw [←neg_add', neg_add_eq_sub, ←neg_sub, ←neg_mem_Ioo_iff] at ht
  rw [Function.comp_apply, Pi.neg_apply, ←neg_one_smul ℝ (v (γ (-t))),
    ←ContinuousLinearMap.smulRight_comp]
  apply (h2 (-t) ht).comp t ⟨continuousAt_neg, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasDerivAt.hasFDerivAt (hasDerivAt_neg _)

lemma isIntegralCurveAt_comp_neg {γ : ℝ → M} :
    IsIntegralCurveAt γ v t₀ x₀ ↔ IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) x₀ := by
  refine ⟨fun hγ => IsIntegralCurveAt.comp_neg hγ, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ => IsIntegralCurveAt.comp_mul_ne_zero hγ ha, fun hγ ↦ ?_⟩
  have := hγ.comp_mul_ne_zero (inv_ne_zero ha)
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, ←div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self ha, div_one, Function.comp.assoc] at this
  convert this
  ext
  simp [inv_mul_eq_div, div_self ha]

variable (t₀) in
lemma isIntegralCurveAt_const (h : v x₀ = 0) : IsIntegralCurveAt (fun _ => x₀) v t₀ x₀ := by
  refine ⟨rfl, 1, zero_lt_one, fun t _ => ?_⟩
  rw [h, ←ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
    ContinuousLinearMap.smulRight_one_one]
  exact hasMFDerivAt_const ..

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector
  of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around
  `t₀`.-/
theorem exists_integralCurve_of_contMDiff_tangent_section (hx : I.IsInteriorPoint x₀) :
    ∃ (γ : ℝ → M), IsIntegralCurveAt γ v t₀ x₀ := by
  -- express the differentiability of the section `v` in the local charts
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, ε1, hε1, hf2⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀
      (hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  rw [←Real.ball_eq_Ioo] at hf2
  -- use continuity of `f` to extract `ε2` so that for `t ∈ Real.ball t₀ ε2`,
  -- `f t ∈ interior (extChartAt I x₀).target`
  have hcont := (hf2 t₀ (Metric.mem_ball_self hε1)).continuousAt
  rw [continuousAt_def, hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀ :=
    hcont _ (isOpen_interior.mem_nhds (ModelWithCorners.isInteriorPoint_iff.mp hx))
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ε2, hε2, hf3⟩ := hnhds
  simp_rw [subset_def, mem_preimage] at hf3
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, LocalEquiv.left_inv _ (mem_extChartAt_source ..)]),
    min ε1 ε2, lt_min hε1 hε2, ?_⟩
  intros t ht
  -- collect useful terms in convenient forms
  rw [←Real.ball_eq_Ioo] at ht
  have hf3 := hf3 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_right ..))
  have h : HasDerivAt f
    ((fderivWithin ℝ ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
        (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
      (v ((extChartAt I x₀).symm (f t))))
    t := hf2 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left ..))
  rw [←tangentCoordChange_def] at h
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source I ((extChartAt I x₀).symm (f t))
  -- express the derivative of the integral curve in the local chart
  refine ⟨ContinuousAt.comp (continuousAt_extChartAt_symm'' _ _ hf3') (h.continuousAt),
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  show HasDerivAt (((extChartAt I ((extChartAt I x₀).symm (f t))) ∘ (extChartAt I x₀).symm) ∘ f)
    (v ((extChartAt I x₀).symm (f t))) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [←tangentCoordChange_self (I := I) (x := (extChartAt I x₀).symm (f t))
      (z := (extChartAt I x₀).symm (f t)) (v := v ((extChartAt I x₀).symm (f t))) hft2,
    ←tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  nth_rw 4 [←(extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_integralCurve_of_contMDiff_tangent_section_boundaryless [I.Boundaryless] :
    ∃ (γ : ℝ → M), IsIntegralCurveAt γ v t₀ x₀ :=
  exists_integralCurve_of_contMDiff_tangent_section hv I.isInteriorPoint
