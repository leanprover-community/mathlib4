/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

Assume `v` is continuously differentiable. The existence theorem for solutions to ODEs implies that
a unique local integral curve exists for any continuously differentiable vector field `v`. The
uniqueness theorem for solutions to ODEs implies that integral curves of `v` are unique. These are
the main results of this file.

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

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a to-do.

The uniqueness theorem requires the manifold to be Hausdorff (T2), so that the set on which two
continuous functions agree is closed.

We state simpler versions of the theorem for manifolds without boundary as corollaries.

## To-do

- The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
  J. M. Lee. May require submanifolds.

## Tags

integral curve, vector field, local existence, uniqueness
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
  ∃ s ∈ nhds t, IsIntegralCurveOn γ v s

/-- If `v : M → TM` is a vector field on `M`, `IsIntegralCurve γ v` means `γ : ℝ → M` is a global
  integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ => h t

lemma isIntegralCurve_iff_isIntegralCurveOn :
    IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h => h.isIntegralCurveOn _, fun h t => h t (mem_univ _)⟩

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t := ⟨univ, Filter.univ_mem, fun t _ => h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := h t
    exact h t (mem_of_mem_nhds hs)⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht => h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.of_union (h : IsIntegralCurveOn γ v s) (h' : IsIntegralCurveOn γ v s') :
    IsIntegralCurveOn γ v (s ∪ s') := by
  intros t ht
  rw [mem_union] at ht
  cases' ht with ht ht
  · exact h _ ht
  · exact h' _ ht

lemma isIntegralCurveAt_iff :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  constructor
  · intro h
    obtain ⟨s, hs, h⟩ := h
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
    exact ⟨ε, hε, h.mono hsub⟩
  · intro h
    obtain ⟨ε, hε, h⟩ := h
    refine ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ nhds t₀) :
    IsIntegralCurveAt γ v t₀ := ⟨s, hs, h⟩

lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s, hs, h⟩ := h t ht
  exact h t (mem_of_mem_nhds hs)

lemma IsIntegralCurveOn.congr_of_eqOn (hs : IsOpen s) (h : IsIntegralCurveOn γ v s)
    (hγ : EqOn γ γ' s) : IsIntegralCurveOn γ' v s := by
  intros t ht
  rw [← hγ ht]
  apply (h t ht).congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem (hs.mem_nhds ht) hγ.symm

lemma IsIntegralCurveAt.congr_of_eventuallyEq (h : IsIntegralCurveAt γ v t₀)
    (hγ : γ =ᶠ[nhds t₀] γ') : IsIntegralCurveAt γ' v t₀ := by
  obtain ⟨ε, hε, h⟩ := h
  obtain ⟨s, hs, heqon⟩ := hγ.exists_mem
  obtain ⟨ε', hε', hss⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min ε ε', lt_min hε hε', ?_⟩
  rw [← Real.ball_eq_Ioo] at *
  intros t ht
  have hh := h t (mem_of_mem_of_subset ht (Metric.ball_subset_ball (min_le_left _ _)))
  rw [← heqon (mem_of_mem_of_subset ht
    (subset_trans (Metric.ball_subset_ball (min_le_right _ _)) hss))]
  apply hh.congr_of_eventuallyEq
  rw [← Metric.isOpen_ball.mem_nhds_iff, Metric.mem_nhds_iff] at ht
  obtain ⟨ε'', hε'', ht⟩ := ht
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Metric.ball t ε'', Metric.ball_mem_nhds _ hε'', ?_⟩
  apply heqon.symm.mono
  apply subset_trans ht
  apply subset_trans _ hss
  exact Metric.ball_subset_ball (min_le_right _ _)

lemma IsIntegralCurve.congr (h : IsIntegralCurve γ v) (hγ : γ = γ') :
    IsIntegralCurve γ' v := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  apply h.congr_of_eqOn isOpen_univ <| (eqOn_univ γ γ').mpr hγ

/-! ### Translation lemmas -/

section Translation

lemma IsIntegralCurveOn.comp_add (hγ : IsIntegralCurveOn γ v s) (dt : ℝ) :
    IsIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  intros t ht
  rw [Function.comp_apply,
    ← ContinuousLinearMap.comp_id (ContinuousLinearMap.smulRight 1 (v (γ (t + dt))))]
  apply HasMFDerivAt.comp t (hγ (t + dt) ht)
  refine ⟨(continuous_add_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasFDerivAt.add_const (hasFDerivAt_id _) _

lemma isIntegralCurveOn_comp_add {dt : ℝ} :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ => ?_⟩
  have := hγ.comp_add (-dt)
  simp only [mem_setOf_eq, neg_add_cancel_right, setOf_mem_eq] at this
  convert this
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isIntegralCurveAt_iff] at hγ
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨Metric.ball (t₀ - dt) ε, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε), ?_⟩
  convert h.comp_add dt
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, dist_sub_eq_dist_add_right]

lemma isIntegralCurveAt_comp_add {dt : ℝ} :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ ↦ ?_⟩
  have := hγ.comp_add (-dt)
  rw [sub_neg_eq_add, sub_add_cancel] at this
  convert this
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_add _

lemma isIntegralCurve_comp_add {dt : ℝ} :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ => hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]

end Translation

/-! ### Scaling lemmas -/

section Scaling

lemma IsIntegralCurveOn.comp_mul (hγ : IsIntegralCurveOn γ v s) (a : ℝ) :
    IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  intros t ht
  rw [Function.comp_apply, Pi.smul_apply, ← ContinuousLinearMap.smulRight_comp]
  refine HasMFDerivAt.comp t (hγ (t * a) ht) ⟨(continuous_mul_right _).continuousAt, ?_⟩
  simp only [mfld_simps, hasFDerivWithinAt_univ]
  exact HasFDerivAt.mul_const' (hasFDerivAt_id _) _

lemma isIntegralCurvOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  refine ⟨fun hγ => hγ.comp_mul a, fun hγ ↦ ?_⟩
  have := hγ.comp_mul a⁻¹
  simp_rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, mem_setOf_eq, mul_assoc,
    inv_mul_eq_div, div_self ha, mul_one, setOf_mem_eq] at this
  convert this
  ext t
  rw [Function.comp_apply, Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]

lemma IsIntegralCurveAt.comp_mul_ne_zero (hγ : IsIntegralCurveAt γ v t₀) {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  obtain ⟨ε, hε, h⟩ := isIntegralCurveAt_iff.mp hγ
  rw [isIntegralCurveAt_iff]
  refine ⟨ε / |a|, div_pos hε (abs_pos.mpr ha), ?_⟩
  convert h.comp_mul a
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, Real.dist_eq, Real.dist_eq,
    lt_div_iff (abs_pos.mpr ha), ← abs_mul, sub_mul, div_mul_cancel _ ha]

lemma isIntegralCurveAt_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· * a)) (a • v) (t₀ / a) := by
  refine ⟨fun hγ => hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
  have := hγ.comp_mul_ne_zero (inv_ne_zero ha)
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul, ← div_mul_eq_div_div_swap,
    inv_mul_eq_div, div_self ha, div_one, Function.comp.assoc] at this
  convert this
  ext t
  simp [inv_mul_eq_div, div_self ha]

lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_mul _

lemma isIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ => hγ.comp_mul _, fun hγ => ?_⟩
  have := hγ.comp_mul a⁻¹
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul] at this
  convert this
  ext t
  rw [Function.comp_apply, Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
  is a global integral curve of `v`. -/
lemma isIntegralCurve_const {x : M} (h : v x = 0) : IsIntegralCurve (fun _ => x) v := by
  intro t
  rw [h, ← ContinuousLinearMap.zero_apply (R₁ := ℝ) (R₂ := ℝ) (1 : ℝ),
    ContinuousLinearMap.smulRight_one_one]
  exact hasMFDerivAt_const ..

lemma IsIntegralCurveOn.continuousAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousAt γ t₀ := (hγ t₀ ht).1

lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht => (hγ t ht).1.continuousWithinAt

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ := by
  obtain ⟨ε, hε, hγ⟩ := hγ
  apply hγ.continuousAt
  exact mem_of_mem_nhds hε

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) :
    Continuous γ := continuous_iff_continuousAt.mpr
      fun _ => (hγ.isIntegralCurveOn univ).continuousAt (mem_univ _)

end Scaling

variable (t₀) {x₀ : M}

/-- For any continuously differentiable vector field and any chosen non-boundary point `x₀` on the
  manifold, there exists an integral curve `γ : ℝ → M` such that `γ t₀ = x₀` and the tangent vector
  of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open interval around
  `t₀`.-/
theorem exists_isIntegralCurveAt_of_contMDiffAt
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
  -- express the differentiability of the vector field `v` in the local chart
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  -- use Picard-Lindelöf theorem to extract a solution to the ODE in the local chart
  obtain ⟨f, hf1, hf2⟩ := exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt t₀
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hx)).snd
  simp_rw [← Real.ball_eq_Ioo, ← Metric.eventually_nhds_iff_ball] at hf2
  -- use continuity of `f` so that `f t` remains inside `interior (extChartAt I x₀).target`
  have ⟨a, ha, hf2'⟩ := Metric.eventually_nhds_iff_ball.mp hf2
  have hcont := (hf2' t₀ (Metric.mem_ball_self ha)).continuousAt
  rw [continuousAt_def, hf1] at hcont
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ nhds t₀ :=
    hcont _ (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx))
  rw [← eventually_mem_nhds] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hf2.and hnhds).exists_mem
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, PartialEquiv.left_inv _ (mem_extChartAt_source ..)]),
    s, hs, ?_⟩
  intros t ht
  -- collect useful terms in convenient forms
  have h : HasDerivAt f
    ((fderivWithin ℝ ((extChartAt I x₀) ∘ (extChartAt I ((extChartAt I x₀).symm (f t))).symm)
        (range I) (extChartAt I ((extChartAt I x₀).symm (f t)) ((extChartAt I x₀).symm (f t))))
      (v ((extChartAt I x₀).symm (f t))))
    t := (haux t ht).1
  rw [← tangentCoordChange_def] at h
  have hf3 := mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source I ((extChartAt I x₀).symm (f t))
  -- express the derivative of the integral curve in the local chart
  refine ⟨(continuousAt_extChartAt_symm'' _ _ hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  show HasDerivAt (((extChartAt I ((extChartAt I x₀).symm (f t))) ∘ (extChartAt I x₀).symm) ∘ f)
    (v ((extChartAt I x₀).symm (f t))) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [← tangentCoordChange_self (I := I) (x := (extChartAt I x₀).symm (f t))
      (z := (extChartAt I x₀).symm (f t)) (v := v ((extChartAt I x₀).symm (f t))) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  nth_rw 4 [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless [I.Boundaryless]
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt t₀ hv I.isInteriorPoint

variable (I)

lemma IsIntegralCurveOn.hasDerivAt (hγ : IsIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      ((tangentCoordChange I (γ t) (γ t₀) (γ t)) (v (γ t))) t := by
  -- turn `HasDerivAt` into comp of `HasMFDerivAt`
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  have hsub : ContinuousLinearMap.comp
      (mfderiv I I (↑(chartAt H (γ t₀))) (γ t))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (v (γ t))) =
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      ((tangentCoordChange I (γ t) (γ t₀) (γ t)) (v (γ t))) := by
    rw [ContinuousLinearMap.ext_iff]
    intro a
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.map_smul_of_tower,
      ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply]
    congr
    have := mdifferentiableAt_atlas I (ChartedSpace.chart_mem_atlas _)
      ((extChartAt_source I (γ t₀)) ▸ hsrc)
    rw [tangentCoordChange_def, mfderiv, if_pos this]
    rfl
  rw [← hsub]
  apply HasMFDerivAt.comp t _ (hγ _ ht)
  apply hasMFDerivAt_extChartAt
  rw [← extChartAt_source I]
  exact hsrc

/-- Local integral curves are unique.

  If a continuously differentiable vector field `v` admits two local integral curves `γ γ' : ℝ → M`
  at `t₀` with `γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval around `t₀` -/
theorem isIntegralCurveAt_eqOn_of_contMDiffAt (ht₀ : I.IsInteriorPoint (γ t₀))
    (hv : ContMDiffAt I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    ∃ ε > 0, EqOn γ γ' (Ioo (t₀ - ε) (t₀ + ε)) := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x =>
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'

  -- extract set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ nhds _, LipschitzOnWith K v' s :=
    ContDiffAt.exists_lipschitzOnWith (hv.contDiffAt (range_mem_nhds_isInteriorPoint ht₀)).snd
  have hlip : ∀ t : ℝ, LipschitzOnWith K ((fun _ => v') t) ((fun _ => s) t) := fun _ => hlip

  -- `γ t` when expressed in the local chart should remain inside `s`
  have hcont : ContinuousAt ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
    (continuousAt_extChartAt ..).comp hγ.continuousAt
  rw [continuousAt_def] at hcont
  have hnhds := hcont _ hs
  rw [← eventually_mem_nhds] at hnhds

  -- `γ t` should remain inside the domain of the local chart around `γ t₀`
  have hsrc := continuousAt_def.mp hγ.continuousAt _ <| extChartAt_source_mem_nhds I (γ t₀)
  rw [← eventually_mem_nhds] at hsrc

  -- `γ` is tangent to `v` in some neighbourhood of `t₀`
  simp_rw [IsIntegralCurveAt, IsIntegralCurveOn, ← Filter.eventually_iff_exists_mem] at hγ

  -- same as above but for `γ'`
  have hcont' : ContinuousAt ((extChartAt I (γ' t₀)) ∘ γ') t₀ :=
    ContinuousAt.comp (continuousAt_extChartAt ..) hγ'.continuousAt
  rw [continuousAt_def] at hcont'
  have hnhds' := hcont' _ (h ▸ hs)
  rw [← eventually_mem_nhds] at hnhds'

  have hsrc' := continuousAt_def.mp hγ'.continuousAt _ <| extChartAt_source_mem_nhds I (γ' t₀)
  rw [← eventually_mem_nhds] at hsrc'

  simp_rw [IsIntegralCurveAt, IsIntegralCurveOn, ← Filter.eventually_iff_exists_mem] at hγ'

  -- there exists a neighbourhood around `t₀` in which all of the above hold
  have haux := hnhds.and <| hsrc.and <| hγ.and <| hnhds'.and <| hsrc'.and hγ'
  rw [Metric.eventually_nhds_iff_ball] at haux

  obtain ⟨ε, hε, haux⟩ := haux
  refine ⟨ε, hε, ?_⟩

  -- break out all the conditions again
  have hmem := fun t ht => mem_preimage.mp <| mem_of_mem_nhds (haux t ht).1
  have hsrc := fun t ht => mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.1
  have hmfd : IsIntegralCurveOn _ _ _ := fun t ht => (haux t ht).2.2.1
  have hmem' := fun t ht => mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.2.2.1
  have hsrc' := fun t ht => mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.2.2.2.1
  have hmfd' : IsIntegralCurveOn _ _ _ := fun t ht => (haux t ht).2.2.2.2.2

  -- `γ` and `γ'` when expressed in the local chart are continuous on this neighbourhood
  have hcont := (continuousOn_extChartAt I (γ t₀)).comp
    (IsIntegralCurveOn.continuousOn hmfd) hsrc
  have hcont' := (continuousOn_extChartAt I (γ' t₀)).comp
    (IsIntegralCurveOn.continuousOn hmfd') hsrc'

  -- todo: make up your mind whether to use `ball` or `Ioo`
  simp_rw [Real.ball_eq_Ioo] at hmem hsrc hmfd hcont hmem' hsrc' hmfd' hcont'

  -- `γ` and `γ'` are
  have heqon : EqOn ((extChartAt I (γ t₀)) ∘ γ) ((extChartAt I (γ' t₀)) ∘ γ')
    (Ioo (t₀ - ε) (t₀ + ε)) := by
    -- uniqueness of ODE solutions in an open interval
    apply ODE_solution_unique_of_mem_set_Ioo hlip (t₀ := t₀)
      (Real.ball_eq_Ioo _ _ ▸ (Metric.mem_ball_self hε)) hcont _ hmem hcont' _ hmem' (by simp [h])
    · intros t ht
      rw [hv']
      have := hmfd.hasDerivAt I t₀ ht (hsrc t ht)
      apply this.hasFDerivAt.congr_fderiv -- missing `hasDerivAt.congr_deriv` ?
      have : γ t = (extChartAt I (γ t₀)).symm (((extChartAt I (γ t₀)) ∘ γ) t) := by
        rw [Function.comp_apply, PartialEquiv.left_inv]
        exact hsrc t ht
      rw [this]
    · intros t ht
      rw [hv', h]
      have := hmfd'.hasDerivAt I t₀ ht (hsrc' t ht)
      apply this.hasFDerivAt.congr_fderiv
      have : γ' t = (extChartAt I (γ' t₀)).symm (((extChartAt I (γ' t₀)) ∘ γ') t) := by
        rw [Function.comp_apply, PartialEquiv.left_inv]
        exact hsrc' t ht
      rw [this]

  -- finally show `EqOn γ γ' _` by composing with the inverse of the local chart around `γ t₀`
  refine EqOn.trans ?_ (EqOn.trans (heqon.comp_left (g := (extChartAt I (γ t₀)).symm)) ?_)
  · intros t ht
    rw [Function.comp_apply, Function.comp_apply, PartialEquiv.left_inv _ (hsrc _ ht)]
  · intros t ht
    rw [Function.comp_apply, Function.comp_apply, h, PartialEquiv.left_inv _ (hsrc' _ ht)]

/-- Integral curves are unique on open intervals.

  If a continuously differentiable vector field `v` admits two integral curves `γ γ' : ℝ → M`
  on some open interval `Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'`
  agree on `Ioo a b`. -/
theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M}
    {a b : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hip : ∀ t ∈ Ioo a b, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  /-
  strategy:
  * Lee P.213, just need to translate "S is closed in J" to type theory language
  -/
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  have hsub : Ioo a b ⊆ s := by
    apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
      ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
    · -- is this really the most convenient way to pass to subtype topology?
      rw [hs, ← Subtype.image_preimage_val, ← Subtype.image_preimage_val,
        image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
      intros t ht
      rw [mem_preimage, ← closure_subtype] at ht
      revert ht t
      apply IsClosed.closure_subset
      apply isClosed_eq
      · rw [continuous_iff_continuousAt]
        rintro ⟨_, ht⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        rw [Subtype.coe_mk]
        exact hγ.continuousAt ht
      · rw [continuous_iff_continuousAt]
        rintro ⟨_, ht⟩
        apply ContinuousAt.comp _ continuousAt_subtype_val
        rw [Subtype.coe_mk]
        exact hγ'.continuousAt ht
    · rw [isOpen_iff_mem_nhds]
      intro t₁ ht₁
      rw [mem_nhds_iff]
      obtain ⟨ε, hε, heqon⟩ : ∃ ε > 0, EqOn γ γ' (Ioo (t₁ - ε) (t₁ + ε)) :=
        isIntegralCurveAt_eqOn_of_contMDiffAt I _ (hip _ ht₁.2) hv.contMDiffAt
          (hγ.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
          (hγ'.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
          ht₁.1
      refine ⟨Ioo (max a (t₁ - ε)) (min b (t₁ + ε)),
        subset_inter
          (fun t ht => @heqon t <| mem_of_mem_of_subset ht <| Ioo_subset_Ioo (by simp) (by simp))
          (Ioo_subset_Ioo (by simp) (by simp)),
        isOpen_Ioo, ?_⟩
      rw [mem_Ioo]
      constructor
      · apply max_lt ht₁.2.1
        simp [hε]
      · apply lt_min ht₁.2.2
        simp [hε]
  intros t ht
  exact mem_setOf.mp ((subset_def ▸ hsub) t ht).1

/-- Global integral curves are unique. -/
theorem isIntegralCurve_eq_of_contMDiff {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x} {γ γ' : ℝ → M}
    (hip : ∀ t, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  obtain ⟨T, hT, ht⟩ : ∃ T > 0, t ∈ Ioo (t₀ - T) (t₀ + T) := by
    refine ⟨2 * |t - t₀| + 1, add_pos_of_nonneg_of_pos (by simp) zero_lt_one, ?_⟩
    rw [mem_Ioo]
    by_cases ht : t - t₀ < 0
    · rw [abs_of_neg ht]
      constructor <;> linarith
    · rw [abs_of_nonneg (not_lt.mp ht)]
      constructor <;> linarith
  exact isIntegralCurveOn_Ioo_eqOn_of_contMDiff I t₀
    (Real.ball_eq_Ioo t₀ T ▸ Metric.mem_ball_self hT) (fun t _ => hip t) hv
    (IsIntegralCurveOn.mono (hγ.isIntegralCurveOn _) (subset_univ _))
    (IsIntegralCurveOn.mono (hγ'.isIntegralCurveOn _) (subset_univ _)) h ht

-- extend an integral curve by another one
lemma isIntegralCurveOn_piecewise [I.Boundaryless] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {γ γ' : ℝ → M}
    {a b a' b' : ℝ} (hγ : IsIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' v (Ioo a' b')) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsIntegralCurveOn (piecewise (Ioo a b) γ γ') v (Ioo a b ∪ Ioo a' b') := by
  intros t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, if_pos hmem]
    apply (hγ t hmem).congr_of_eventuallyEq
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, Ioo_mem_nhds hmem.1 hmem.2, ?_⟩
    intros t' ht'
    rw [piecewise, if_pos ht']
  · rw [piecewise, if_neg hmem]
    rw [mem_union] at ht
    have hmem' := Classical.or_iff_not_imp_left.mp ht hmem
    apply (hγ' t hmem').congr_of_eventuallyEq
    rw [Filter.eventuallyEq_iff_exists_mem]
    rw [mem_Ioo, not_and, not_lt] at hmem
    by_cases hlt : a < t
    · by_cases hb : t = b
      · refine ⟨Ioo (max a a') b', Ioo_mem_nhds (max_lt hlt hmem'.1) hmem'.2, ?_⟩
        have : Ioo (max a a') b ∪ Ico b b' = Ioo (max a a') b' := by
          apply Ioo_union_Ico_eq_Ioo
          · rw [max_lt_iff, ← hb]
            exact ⟨hlt, hmem'.1⟩
          · rw [← hb]
            exact le_of_lt hmem'.2
        rw [← this]
        apply EqOn.union
        · have heqon : EqOn γ (piecewise (Ioo a b) γ γ') (Ioo (max a a') b) := by
            intros t' ht'
            rw [piecewise, if_pos]
            refine ⟨(max_lt_iff.mp ht'.1).1, ht'.2⟩
          apply isIntegralCurveOn_Ioo_eqOn_of_contMDiff I t₀ _ _ hv
          · apply IsIntegralCurveOn.congr_of_eqOn isOpen_Ioo (γ := γ) _ heqon
            apply hγ.mono
            exact Ioo_subset_Ioo (le_max_left _ _) le_rfl
          · apply hγ'.mono
            apply Ioo_subset_Ioo (le_max_right _ _)
            rw [← hb]
            exact le_of_lt hmem'.2
          · rw [piecewise, if_pos ht₀.1]
            exact h
          · exact ⟨max_lt ht₀.1.1 ht₀.2.1, ht₀.1.2⟩
          · intros
            exact ModelWithCorners.isInteriorPoint
        · intros t' ht'
          rw [piecewise, if_neg]
          exact not_mem_Ioo_of_ge ht'.1
      · refine ⟨Ioo b b', Ioo_mem_nhds (lt_of_le_of_ne (hmem hlt) (Ne.symm hb)) hmem'.2, ?_⟩
        intros t' ht'
        have : t' ∉ Ioo a b := not_mem_Ioo_of_ge (le_of_lt ht'.1)
        rw [piecewise, if_neg this]
    · by_cases ha : t = a
      · refine ⟨Ioo a' (min b b'),
          Ioo_mem_nhds hmem'.1 (lt_min (ha ▸ lt_trans ht₀.1.1 ht₀.1.2) hmem'.2), ?_⟩
        have : Ioc a' a ∪ Ioo a (min b b') = Ioo a' (min b b') := by
          apply Ioc_union_Ioo_eq_Ioo
          · rw [← ha]
            exact le_of_lt hmem'.1
          · rw [lt_min_iff]
            exact ⟨lt_trans ht₀.1.1 ht₀.1.2, ha ▸ hmem'.2⟩
        rw [← this]
        apply EqOn.union
        · intros t' ht'
          rw [piecewise, if_neg]
          exact not_mem_Ioo_of_le ht'.2
        · have heqon : EqOn γ (piecewise (Ioo a b) γ γ') (Ioo a (min b b')) := by
            intros t' ht'
            rw [piecewise, if_pos]
            exact ⟨ht'.1, (lt_min_iff.mp ht'.2).1⟩
          apply isIntegralCurveOn_Ioo_eqOn_of_contMDiff I t₀ _ _ hv
          · apply IsIntegralCurveOn.congr_of_eqOn isOpen_Ioo (γ := γ) _ heqon
            apply hγ.mono
            exact Ioo_subset_Ioo le_rfl (min_le_left _ _)
          · apply hγ'.mono
            apply Ioo_subset_Ioo _ (min_le_right _ _)
            rw [← ha]
            exact le_of_lt hmem'.1
          · rw [piecewise, if_pos ht₀.1]
            exact h
          · exact ⟨ht₀.1.1, lt_min ht₀.1.2 ht₀.2.2⟩
          · intros
            exact ModelWithCorners.isInteriorPoint
      · refine ⟨Ioo a' a, Ioo_mem_nhds hmem'.1 (lt_of_le_of_ne (not_lt.mp hlt) ha), ?_⟩
        intros t' ht'
        have : t' ∉ Ioo a b := not_mem_Ioo_of_le (le_of_lt ht'.2)
        rw [piecewise, if_neg this]

lemma Ioo_union_Ioo_eq_Ioo {α : Type*} [LinearOrder α] {a : α} {b : α} {c : α} {d : α}
    (hab : a < b) (hbc : b < c) (hcd : c < d) : Ioo a c ∪ Ioo b d = Ioo a d := by
  rw [Ioo_union_Ioo, min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hcd)]
  · rw [min_eq_left (le_of_lt (lt_trans hab hbc)), max_eq_right (le_of_lt (lt_trans hbc hcd))]
    exact lt_trans (lt_trans hab hbc) hcd
  · rw [min_eq_left (le_of_lt (lt_trans hbc hcd)), max_eq_right (le_of_lt (lt_trans hab hbc))]
    exact hbc

/-- If there exists `ε > 0` such that the local integral curve at each point `x : M` is defined at
  least on an open interval `Ioo (-ε) ε`, then every point on `M` has a global integral
  curve passing through it.

  See Lemma 9.15, Lee -/
lemma exists_isIntegralCurve_of_isIntegralCurveOn [I.Boundaryless] {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [SmoothManifoldWithCorners I M] [T2Space M] {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε) (h : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-ε) ε))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurve γ v := by

  /-
  Strategy:
  * consider `S := {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)}`
  * `S` is non-empty by assumption
  * suppose `S` is bounded above
  ** we wish to reach a contradiction
  ** define `asup = sSup S`
  ** using `ε / 2` from the hypothesis, there exists `a ∈ S` such that `asup < a + ε / 2`
  ** using this `a`, we obtain a local integral curve `γ` on `Ioo -a a`
  ** obtain a local integral curve `γ1` starting at `-(a - ε / 2)` with radius `ε`
  ** obtain a local integral curve `γ2` starting at `a - ε / 2` with radius `ε`
  ** extend the original local integral curve to `γ_ext`, now defined on
    `Ioo -(a + ε / 2) (a + ε / 2)`
  ** this means `a + ε / 2 ∈ S`, but `asup < a + ε / 2`, which is impossible as `sSup S`
  * suppose `S` is not bounded above (this can be a separate lemma)
  ** for every `a : ℝ`, there is `a' ∈ S` such that `a < a'`
  ** construct a global integral curve `γ` as follows
  *** for each `n : ℕ`, define `γ_aux n` to be some local integral curve on `Ioo -n n`
  *** for each `t : ℝ`, define `γ t = γ_aux ⌈|t|⌉₊ t`
  *** if `t` is not an integer, then `γ` is locally equal to `γ_aux ⌈|t|⌉₊`, which is a local
    integral curve
  *** if `t` is an integer, then we can use the uniqueness theorem to show that `γ` is locally equal
    to `γ_aux (t + 1)`, since `γ_aux t` and `γ_aux (t + 1)` have the same initial condition
  ** that's the global integral curve we need

  `hbdd : ∀ (t : ℝ), ∃ a, (∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)) ∧ t < a`
  `Classical.choose (hbdd n)` picks `a > n` such that some integral curve is defined on `Ioo -n n`
  `Classical.choose (Classical.choose_spec (hbdd n)).1` picks such an integral curve

  -/

  have hnon : Set.Nonempty {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} := ⟨ε, h x⟩
  by_cases hbdd : BddAbove {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)}
  · set asup := sSup {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} with hasup
    obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup hnon (ε := - (ε / 2))
      (by rw [neg_lt, neg_zero]; exact half_pos hε)
    rw [mem_setOf] at ha
    rw [← hasup] at hlt
    have hlt' : ε / 2 < a := by
      apply lt_of_le_of_lt _ hlt
      rw [le_add_neg_iff_add_le, ← mul_two, div_mul_cancel _ two_ne_zero, hasup]
      apply le_csSup hbdd
      rw [mem_setOf]
      exact h x
    obtain ⟨γ, h0, hγ⟩ := ha
    obtain ⟨γ1_aux, h1_aux, hγ1_aux⟩ := h (γ (-(a - ε / 2)))
    let γ1 := γ1_aux ∘ (fun t => t + (a - ε / 2))
    have h1 : γ1 (-(a - ε / 2)) = γ (-(a - ε / 2)) := by
      simp [h1_aux]
    have hγ1 : IsIntegralCurveOn γ1 v (Ioo (-(a + ε / 2)) (-(a - 3 * ε / 2))) := by
      convert hγ1_aux.comp_add (a - ε / 2)
      ext t
      rw [mem_Ioo, mem_setOf, mem_Ioo, ← sub_lt_iff_lt_add, neg_sub_left, sub_add_eq_add_sub,
        ← add_sub, sub_self_div_two, ← lt_sub_iff_add_lt, ← sub_add, sub_add_eq_add_sub,
        add_div_eq_mul_add_div (a := ε) (hc := two_ne_zero)]
      nth_rw 5 [← mul_one (a := ε)]
      rw [← mul_add, two_add_one_eq_three, mul_comm (a := ε), neg_sub]
    obtain ⟨γ2_aux, h2_aux, hγ2_aux⟩ := h (γ (a - ε / 2))
    let γ2 := γ2_aux ∘ (fun t => t + -(a - ε / 2))
    have h2 : γ2 (a - ε / 2) = γ (a - ε / 2) := by
      simp [h2_aux]
    have hγ2 : IsIntegralCurveOn γ2 v (Ioo (a - 3 * ε / 2) (a + ε / 2)) := by
      convert hγ2_aux.comp_add (-(a - ε / 2))
      ext t
      rw [mem_Ioo, mem_setOf, mem_Ioo, neg_sub, add_sub, lt_sub_iff_add_lt, ← sub_eq_neg_add,
        ← sub_lt_iff_lt_add (b := t), sub_sub, add_div' (b := ε) (hc := two_ne_zero)]
      nth_rw 4 [← mul_one (a := ε)]
      rw [← mul_add, two_add_one_eq_three, sub_lt_iff_lt_add' (c := ε), ← lt_sub_iff_add_lt,
        ← add_sub, sub_self_div_two, mul_comm ε]
    set γ_ext : ℝ → M := piecewise (Ioo (-(a + ε / 2)) a)
      (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
    have hext : IsIntegralCurveOn γ_ext v (Ioo (-(a + ε / 2)) (a + ε / 2)) := by
      have hsub1 : Ioo (-(a + ε / 2)) (a + ε / 2) =
        Ioo (-(a + ε / 2)) a ∪ Ioo (a - 3 * ε / 2) (a + ε / 2) := by
        rw [Ioo_union_Ioo_eq_Ioo] <;> linarith
      rw [hsub1]
      apply isIntegralCurveOn_piecewise I hv (t₀ := a - ε / 2)
      · have hsub2 : Ioo (-(a + ε / 2)) a ⊆
          Ioo (-a) a ∪ Ioo (-(a + ε / 2)) (-(a - 3 * ε / 2)) := by
            intros t ht
            by_cases ht' : -a < t
            · exact mem_union_left _ ⟨ht', ht.2⟩
            · rw [not_lt] at ht'
              apply mem_union_right
              use ht.1
              linarith
        apply IsIntegralCurveOn.mono _ hsub2
        apply isIntegralCurveOn_piecewise I hv hγ hγ1 (t₀ := -(a - ε / 2))
        · rw [mem_inter_iff, mem_Ioo, mem_Ioo, and_assoc, neg_lt_neg_iff, neg_lt_neg_iff,
            neg_lt_neg_iff, neg_lt, sub_lt_self_iff, sub_lt_iff_lt_add, add_assoc, add_halves,
            lt_add_iff_pos_right, sub_lt_sub_iff_left, div_lt_div_right two_pos]
          refine ⟨half_pos hε, by linarith, hε, by linarith⟩
        · exact h1.symm
      · exact hγ2
      · rw [mem_inter_iff, mem_Ioo, mem_Ioo, and_assoc, neg_add', sub_lt_sub_iff_right,
          neg_lt_self_iff, sub_lt_self_iff, sub_lt_sub_iff_left, div_lt_div_right two_pos,
          sub_lt_iff_lt_add, add_assoc, add_halves, lt_add_iff_pos_right]
        refine ⟨?_, half_pos hε, by linarith, hε⟩
        exact lt_trans (half_pos hε) hlt'
      · rw [piecewise, if_pos, h2]
        refine ⟨by linarith, by linarith⟩
    have : a + ε / 2 ∈ {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} := by
      rw [mem_setOf]
      refine ⟨γ_ext, ?_, hext⟩
      rw [γ_ext_def, piecewise, if_pos, piecewise, if_pos, h0]
      · rw [mem_Ioo, neg_lt, neg_zero, and_self]
        apply lt_trans (half_pos hε) hlt'
      · rw [mem_Ioo, neg_lt, neg_zero]
        exact ⟨add_pos (lt_trans (half_pos hε) hlt') (half_pos hε), lt_trans (half_pos hε) hlt'⟩
    rw [add_neg_lt_iff_lt_add, ← not_le] at hlt
    exact absurd (le_csSup hbdd this) hlt
  · rw [not_bddAbove_iff] at hbdd
    simp_rw [mem_setOf] at hbdd
    let γ_aux : ℕ → ℝ → M := fun n => by
      induction n
      case zero =>
        exact Classical.choose (Classical.choose_spec (hbdd 1)).1
      case succ n γ_prev =>
        exact piecewise (Ioo (-(n + 1 : ℝ)) (n + 1)) γ_prev
          (Classical.choose (Classical.choose_spec (hbdd (n + 1 + 1))).1)
    have haux : ∀ n : ℕ, γ_aux n 0 = x ∧
      IsIntegralCurveOn (γ_aux n) v (Ioo (-(n + 1)) (n + 1)) := fun n => by
      induction n
      case zero =>
        rw [← Nat.cast_add_one, Nat.zero_add]
        use (Classical.choose_spec (Classical.choose_spec (hbdd 1)).1).1
        apply (Classical.choose_spec (Classical.choose_spec (hbdd 1)).1).2.mono
        have hlt := (Classical.choose_spec (hbdd 1)).2
        convert Ioo_subset_Ioo (neg_le_neg (le_of_lt hlt)) (le_of_lt hlt) <;> simp
      case succ n hn =>
        have h1 : γ_aux (Nat.succ n) = piecewise (Ioo (-(n + 1 : ℝ)) (n + 1)) (γ_aux n)
          (Classical.choose (Classical.choose_spec (hbdd (n + 1 + 1))).1) := rfl
        have h2 : Ioo (-(n + 1 + 1 : ℝ)) (n + 1 + 1) =
          Ioo (-(n + 1 : ℝ)) (n + 1) ∪ Ioo (-((n : ℝ) + 1 + 1)) (n + 1 + 1) := by
            rw [union_eq_self_of_subset_left]
            exact Ioo_subset_Ioo (by linarith) (by linarith)
        rw [h1, Nat.cast_succ, h2]
        constructor
        · rw [piecewise, if_pos, hn.1]
          constructor
          · rw [neg_lt, neg_zero, ← Nat.cast_add_one, Nat.cast_pos]
            exact Nat.succ_pos _
          · rw [← Nat.cast_add_one, Nat.cast_pos]
            exact Nat.succ_pos _
        · apply isIntegralCurveOn_piecewise I hv hn.2 (t₀ := 0)
          · apply (Classical.choose_spec (Classical.choose_spec (hbdd (n + 1 + 1))).1).2.mono
            have hlt := (Classical.choose_spec (hbdd (n + 1 + 1))).2
            exact Ioo_subset_Ioo (neg_le_neg (le_of_lt hlt)) (le_of_lt hlt)
          · rw [mem_inter_iff, mem_Ioo, mem_Ioo, neg_lt, neg_zero, neg_lt, neg_zero, and_assoc,
              ← Nat.cast_add_one, ← Nat.cast_add_one, Nat.cast_pos, Nat.cast_pos]
            refine ⟨Nat.succ_pos _, Nat.succ_pos _, Nat.succ_pos _, Nat.succ_pos _⟩
          · rw [(Classical.choose_spec (Classical.choose_spec (hbdd (n + 1 + 1))).1).1]
            exact hn.1
    set γ_ext : ℝ → M := fun t => γ_aux (Nat.floor |t|) t with γ_ext_def
    have hext_eq_aux : ∀ n : ℕ, EqOn γ_ext (γ_aux n) (Ioo (-(n + 1 : ℝ)) (n + 1)) := fun n => by
      induction n
      case zero =>
        intros t ht
        rw [γ_ext_def]
        show γ_aux ⌊|t|⌋₊ t = γ_aux 0 t
        have : ⌊|t|⌋₊ = 0 := by
          rw [Nat.floor_eq_zero, abs_lt]
          rw [CharP.cast_eq_zero, zero_add] at ht
          exact ht
        rw [this]
      case succ n hn =>
        intros t ht
        by_cases hmem : t ∈ (Ioo (-(n + 1 : ℝ)) (n + 1))
        · rw [hn hmem]
          -- this should be a separate lemma
          apply isIntegralCurveOn_Ioo_eqOn_of_contMDiff I 0 _ _ hv (haux n).2
          · apply (haux n.succ).2.mono
            apply Ioo_subset_Ioo
            · rw [neg_le_neg_iff, ← Nat.cast_add_one, ← Nat.cast_add_one]
              apply Nat.cast_le_cast
              exact Nat.le_succ _
            · rw [← Nat.cast_add_one, ← Nat.cast_add_one]
              apply Nat.cast_le_cast
              exact Nat.le_succ _
          · rw [(haux n).1, (haux n.succ).1]
          · exact hmem
          · rw [mem_Ioo, neg_lt_zero, ← Nat.cast_add_one, Nat.cast_pos]
            exact ⟨Nat.succ_pos _, Nat.succ_pos _⟩
          · intros
            exact ModelWithCorners.isInteriorPoint
        · rw [γ_ext_def]
          show γ_aux ⌊|t|⌋₊ t = γ_aux (n + 1) t
          have : ⌊|t|⌋₊ = n + 1 := by
            rw [Nat.floor_eq_iff (abs_nonneg _)]
            rw [mem_Ioo, neg_lt] at ht
            by_cases hlt : t < 0
            · rw [abs_of_neg hlt]
              refine ⟨?_, ht.1⟩
              rw [mem_Ioo, not_and', not_lt, le_neg, ← Nat.cast_add_one] at hmem
              apply hmem
              apply lt_trans hlt
              rw [Nat.cast_pos]
              exact Nat.succ_pos _
            · rw [not_lt] at hlt
              rw [abs_of_nonneg hlt]
              refine ⟨?_, ht.2⟩
              rw [mem_Ioo, not_and, not_lt, ← Nat.cast_add_one] at hmem
              apply hmem
              apply lt_of_lt_of_le _ hlt
              rw [neg_lt, neg_zero, Nat.cast_pos]
              exact Nat.succ_pos _
          rw [this]
    refine ⟨γ_ext, by simp [(haux 0).1], ?_⟩
    intro t
    have hmem : t ∈ Ioo (-((⌊|t|⌋₊ : ℝ) + 1)) (⌊|t|⌋₊ + 1) := by
      rw [mem_Ioo]
      by_cases ht : t < 0
      · rw [abs_of_neg ht, neg_lt]
        refine ⟨Nat.lt_floor_add_one _, lt_trans ht ?_⟩
        rw [← Nat.cast_add_one, Nat.cast_pos]
        exact Nat.succ_pos _
      · rw [not_lt] at ht
        rw [abs_of_nonneg ht, neg_lt]
        refine ⟨lt_of_le_of_lt (neg_le_neg ht) ?_, Nat.lt_floor_add_one _⟩
        rw [neg_zero, ← Nat.cast_add_one, Nat.cast_pos]
        exact Nat.succ_pos _
    apply ((haux ⌊|t|⌋₊).2 t hmem).congr_of_eventuallyEq
    apply EqOn.eventuallyEq_of_mem (hext_eq_aux ⌊|t|⌋₊)
    exact Ioo_mem_nhds hmem.1 hmem.2
