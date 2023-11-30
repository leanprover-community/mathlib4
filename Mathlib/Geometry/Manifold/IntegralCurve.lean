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

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
- **`IsIntegralCurve γ v`**: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
integral curve of `v`.
- **`IsIntegralCurveOn γ v s`**: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
- **`IsIntegralCurveAt γ v t₀`**: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsIntegralCurveOn γ v s` and `IsIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## To-do

- Prove `comp_add`, `comp_smul` , etc. lemmas for `IsIntegralCurveOn`, and then derive versions for
`IsIntegralCurveAt` and `IsIntegralCurve` as corollaries.

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

/-- If `γ : ℝ → M`, `v : M → TM` is a vector field on `M`, and `s ∈ Set ℝ`,
  `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. The value of `γ`
  outside of `s` is irrelevant and considered junk.  -/
def IsIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) :=
  ∀ (t : ℝ), t ∈ s → HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

/-- If `v : M → TM` is a vector field on `M`, and `t₀ : ℝ`, `IsIntegralCurveAt γ v t₀` means
  `γ : ℝ → M` is a local integral curve of `v` in an open interval of `t₀`. That is, there exists
  `ε > 0` such that `γ t` is tangent to `v (γ t)` for all `t ∈ Ioo (t₀ - ε) (t₀ + ε)`. The value of
  `γ` outside of this interval is irrelevant and considered junk. -/
def IsIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t : ℝ) :=
  ∃ ε > (0 : ℝ), IsIntegralCurveOn γ v (Ioo (t - ε) (t + ε))

/-- If `v : M → TM` is a vector field on `M`, `IsIntegralCurve γ v` means `γ : ℝ → M` is a global
  integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

lemma IsIntegralCurve.isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (h : IsIntegralCurve γ v) (s : Set ℝ) : IsIntegralCurveOn γ v s := fun t _ => h t

lemma isIntegralCurve_iff_isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x} :
    IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h => h.isIntegralCurveOn _, fun h t => h t (mem_univ _)⟩

lemma IsIntegralCurve.isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x}
    (h : IsIntegralCurve γ v) (t : ℝ) : IsIntegralCurveAt γ v t :=
  ⟨1, zero_lt_one, fun t _ => h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x} :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨ε, hε, h⟩ := h t
    exact h t (Real.ball_eq_Ioo _ _ ▸ Metric.mem_ball_self hε)⟩

lemma IsIntegralCurveOn.mono {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : IsIntegralCurveOn γ v s) {s' : Set ℝ} (hs : s' ⊆ s) : IsIntegralCurveOn γ v s' :=
  fun t ht => h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.isIntegralCurveAt {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : IsIntegralCurveOn γ v s) {t : ℝ} (hs : s ∈ nhds t) : IsIntegralCurveAt γ v t := by
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hε, hmem⟩ := hs
  exact ⟨ε, hε, Real.ball_eq_Ioo _ _ ▸ h.mono hmem⟩

lemma IsIntegralCurveAt.isIntegralCurveOn {γ : ℝ → M} {v : (x : M) → TangentSpace I x} {s : Set ℝ}
    (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) : IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨ε, hε, h⟩ := h t ht
  exact h t (Real.ball_eq_Ioo _ _ ▸ Metric.mem_ball_self hε)

-- variable {t₀}

-- lemma IsIntegralCurveAt.comp_add {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
--     IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
--   obtain ⟨ε, hε, h2⟩ := hγ
--   refine ⟨ε, hε, fun t ht => ?_⟩
--   rw [sub_right_comm, sub_add_eq_add_sub, ← add_mem_Ioo_iff_left] at ht
--   have h2' := h2 (t + dt) ht
--   rw [Function.comp_apply,
--     ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
--   apply HasMFDerivAt.comp t h2'
--   -- this makes me think we need lemmas for `HasMFDerivAt 𝓘(E, E) 𝓘(E, E)` of simple operations
--   refine ⟨(continuous_add_right _).continuousAt, ?_⟩
--   simp only [mfld_simps, hasFDerivWithinAt_univ]
--   exact HasFDerivAt.add_const (hasFDerivAt_id _) _

-- lemma isIntegralCurveAt_comp_add {γ : ℝ → M} {dt : ℝ} : IsIntegralCurveAt γ v t₀ ↔
--     IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
--   refine ⟨fun hγ => IsIntegralCurveAt.comp_add hγ _, fun hγ ↦ ?_⟩
--   have := hγ.comp_add (-dt)
--   rw [sub_neg_eq_add, sub_add_cancel] at this
--   convert this
--   ext
--   simp only [Function.comp_apply, neg_add_cancel_right]

-- lemma IsIntegralCurveAt.comp_mul_pos {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ}
--     (ha : 0 < a) : IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
--   obtain ⟨ε, hε, h2⟩ := hγ
--   refine ⟨ε / a, div_pos hε ha, fun t ht => ?_⟩
--   have ht : t * a ∈ Ioo (t₀ - ε) (t₀ + ε) := by
--     rw [mem_Ioo, ← div_lt_iff ha, ← lt_div_iff ha, sub_div, add_div]
--     exact ht
--   rw [Function.comp_apply, Pi.smul_apply, ← ContinuousLinearMap.smulRight_comp]
--   refine HasMFDerivAt.comp t (h2 (t * a) ht) ⟨(continuous_mul_right _).continuousAt, ?_⟩
--   simp only [mfld_simps, hasFDerivWithinAt_univ]
--   exact HasFDerivAt.mul_const' (hasFDerivAt_id _) _

-- lemma isIntegralCurvAt_comp_mul_pos {γ : ℝ → M} {a : ℝ} (ha : 0 < a) :
--     IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
--   refine ⟨fun hγ => IsIntegralCurveAt.comp_mul_pos hγ ha, fun hγ ↦ ?_⟩
--   have := hγ.comp_mul_pos (inv_pos_of_pos ha)
--   rw [smul_smul, inv_mul_eq_div, div_self (ne_of_gt ha), one_smul, ← div_mul_eq_div_div_swap,
--     inv_mul_eq_div, div_self (ne_of_gt ha), div_one, Function.comp.assoc] at this
--   convert this
--   ext
--   simp [inv_mul_eq_div, div_self (ne_of_gt ha)]

-- lemma IsIntegralCurveAt.comp_neg {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) :
--     IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) := by
--   obtain ⟨ε, hε, h2⟩ := hγ
--   refine ⟨ε, hε, fun t ht => ?_⟩
--   rw [← neg_add', neg_add_eq_sub, ← neg_sub, ← neg_mem_Ioo_iff] at ht
--   rw [Function.comp_apply, Pi.neg_apply, ← neg_one_smul ℝ (v (γ (-t))),
--     ← ContinuousLinearMap.smulRight_comp]
--   apply (h2 (-t) ht).comp t ⟨continuousAt_neg, ?_⟩
--   simp only [mfld_simps, hasFDerivWithinAt_univ]
--   exact HasDerivAt.hasFDerivAt (hasDerivAt_neg _)

-- lemma isIntegralCurveAt_comp_neg {γ : ℝ → M} :
--     IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ Neg.neg) (-v) (-t₀) := by
--   refine ⟨fun hγ => IsIntegralCurveAt.comp_neg hγ, fun hγ ↦ ?_⟩
--   have := hγ.comp_neg
--   rw [Function.comp.assoc, neg_comp_neg, neg_neg, neg_neg] at this
--   exact this

-- lemma IsIntegralCurveAt.comp_mul_ne_zero {γ : ℝ → M} (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ}
--     (ha : a ≠ 0) : IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
--   rw [ne_iff_lt_or_gt] at ha
--   cases' ha with ha ha
--   · apply isIntegralCurveAt_comp_neg.mpr
--     have : (· * a) ∘ Neg.neg = fun t ↦ t * -a := by ext; simp
--     rw [Function.comp.assoc, this, ← neg_smul, ← div_neg]
--     exact hγ.comp_mul_pos (neg_pos_of_neg ha)
--   · exact hγ.comp_mul_pos ha

-- lemma isIntegralCurveAt_comp_mul_ne_zero {γ : ℝ → M} {a : ℝ} (ha : a ≠ 0) :
--     IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
--   refine ⟨fun hγ => IsIntegralCurveAt.comp_mul_ne_zero hγ ha, fun hγ ↦ ?_⟩
--   have := hγ.comp_mul_ne_zero (inv_ne_zero ha)
--   rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, ← div_mul_eq_div_div_swap,
--     inv_mul_eq_div, div_self ha, div_one, Function.comp.assoc] at this
--   convert this
--   ext
--   simp [inv_mul_eq_div, div_self ha]

-- variable (t₀) in
-- /-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
--   is a global integral curve of `v`. -/
-- lemma isIntegralCurve_const (h : v x₀ = 0) : IsIntegralCurve (fun _ => x₀) v := by
--   intro t
--   rw [h, ← ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
--     ContinuousLinearMap.smulRight_one_one]
--   exact hasMFDerivAt_const ..

-- /-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
--   manifold, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector
--   of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around
--   `t₀`.-/
-- theorem exists_isIntegralCurveAt_of_contMDiffAt (hx : I.IsInteriorPoint x₀) :
--     ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
--   -- express the differentiability of the section `v` in the local charts
--   rw [contMDiffAt_iff] at hv
--   obtain ⟨_, hv⟩ := hv
--   -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
--   obtain ⟨f, hf1, ε1, hε1, hf2⟩ :=
--     exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀
--       (hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
--   rw [← Real.ball_eq_Ioo] at hf2
--   -- use continuity of `f` to extract `ε2` so that for `t ∈ Real.ball t₀ ε2`,
--   -- `f t ∈ interior (extChartAt I x₀).target`
--   have hcont := (hf2 t₀ (Metric.mem_ball_self hε1)).continuousAt
--   rw [continuousAt_def, hf1] at hcont
--   have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀ :=
--     hcont _ (isOpen_interior.mem_nhds (ModelWithCorners.isInteriorPoint_iff.mp hx))
--   rw [Metric.mem_nhds_iff] at hnhds
--   obtain ⟨ε2, hε2, hf3⟩ := hnhds
--   simp_rw [subset_def, mem_preimage] at hf3
--   -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
--   refine ⟨(extChartAt I x₀).symm ∘ f,
--     Eq.symm (by rw [Function.comp_apply, hf1, LocalEquiv.left_inv _ (mem_extChartAt_source ..)]),
--     min ε1 ε2, lt_min hε1 hε2, ?_⟩
--   intros t ht
--   -- collect useful terms in convenient forms
--   rw [← Real.ball_eq_Ioo] at ht
--   have hf3 := hf3 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_right ..))
--   have h : HasDerivAt f
--     ((fderivWithin ℝ ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
--         (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
--       (v ((extChartAt I x₀).symm (f t))))
--     t := hf2 t <| mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left ..))
--   rw [← tangentCoordChange_def] at h
--   have hf3' := mem_of_mem_of_subset hf3 interior_subset
--   have hft1 := mem_preimage.mp <|
--     mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
--   have hft2 := mem_extChartAt_source I ((extChartAt I x₀).symm (f t))
--   -- express the derivative of the integral curve in the local chart
--   refine ⟨ContinuousAt.comp (continuousAt_extChartAt_symm'' _ _ hf3') (h.continuousAt),
--     HasDerivWithinAt.hasFDerivWithinAt ?_⟩
--   simp only [mfld_simps, hasDerivWithinAt_univ]
--   show HasDerivAt (((extChartAt I ((extChartAt I x₀).symm (f t))) ∘ (extChartAt I x₀).symm) ∘ f)
--     (v ((extChartAt I x₀).symm (f t))) t
--   -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
--   -- `HasFDerivAt.comp_hasDerivAt` on `h`
--   rw [← tangentCoordChange_self (I := I) (x := (extChartAt I x₀).symm (f t))
--       (z := (extChartAt I x₀).symm (f t)) (v := v ((extChartAt I x₀).symm (f t))) hft2,
--     ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
--   apply HasFDerivAt.comp_hasDerivAt _ _ h
--   apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
--     mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
--       subset_trans interior_subset (extChartAt_target_subset_range ..),
--       isOpen_interior, hf3⟩
--   nth_rw 4 [← (extChartAt I x₀).right_inv hf3']
--   exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

-- /-- For any continuously differentiable vector field defined on a manifold without boundary and any
--   chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
--   tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
--   interval around `t₀`. -/
-- lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless [I.Boundaryless] :
--     ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
--   exists_isIntegralCurveAt_of_contMDiffAt hv I.isInteriorPoint
