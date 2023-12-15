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
    IsIntegralCurveOn γ v s := fun t _ ↦ h t

lemma isIntegralCurve_iff_isIntegralCurveOn : IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isIntegralCurveOn _, fun h t ↦ h t (mem_univ _)⟩

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t := ⟨univ, Filter.univ_mem, fun t _ ↦ h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := h t
    exact h t (mem_of_mem_nhds hs)⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.of_union (h : IsIntegralCurveOn γ v s) (h' : IsIntegralCurveOn γ v s') :
    IsIntegralCurveOn γ v (s ∪ s') := by
  intros t ht
  cases' ht with ht ht
  · exact h _ ht
  · exact h' _ ht

lemma isIntegralCurveAt_iff :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  refine ⟨?_,  fun ⟨ε, hε, h⟩ ↦ ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩⟩
  rintro ⟨s, hs, h⟩
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hs
  exact ⟨ε, hε, h.mono hsub⟩

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ nhds t₀) :
    IsIntegralCurveAt γ v t₀ := ⟨s, hs, h⟩

lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s, hs, h⟩ := h t ht
  exact h t (mem_of_mem_nhds hs)

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
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ ↦ hγ.comp_mul a, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ ↦ hγ.comp_mul_ne_zero ha, fun hγ ↦ ?_⟩
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
  refine ⟨fun hγ ↦ hγ.comp_mul _, fun hγ ↦ ?_⟩
  have := hγ.comp_mul a⁻¹
  rw [smul_smul, inv_mul_eq_div, div_self ha, one_smul] at this
  convert this
  ext t
  rw [Function.comp_apply, Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]

/-- If the vector field `v` vanishes at `x₀`, then the constant curve at `x₀`
  is a global integral curve of `v`. -/
lemma isIntegralCurve_const {x : M} (h : v x = 0) : IsIntegralCurve (fun _ ↦ x) v := by
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
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
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

variable {t₀}

/-- For any continuously differentiable vector field defined on a manifold without boundary and any
  chosen starting point `x₀ : M`, an integral curve `γ : ℝ → M` exists such that `γ t₀ = x₀` and the
  tangent vector of `γ` at `t` coincides with the vector field at `γ t` for all `t` within an open
  interval around `t₀`. -/
lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless [I.Boundaryless]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ (γ : ℝ → M), γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt t₀ hv I.isInteriorPoint

/-- If `γ` is an integral curve of a vector field `v`, then `γ t` is tangent to `v (γ t)` when
  expressed in the local chart around the initial point `γ t₀`. -/
lemma IsIntegralCurveOn.hasDerivAt (hγ : IsIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      ((tangentCoordChange I (γ t) (γ t₀) (γ t)) (v (γ t))) t := by
  -- turn `HasDerivAt` into comp of `HasMFDerivAt`
  have hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t
    (hasMFDerivAt_extChartAt I hsrc) (hγ _ ht)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange I hsrc]
  rfl

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

  simp_rw [Real.ball_eq_Ioo] at hmem hsrc hmfd hcont hmem' hsrc' hmfd' hcont'

  -- `γ` and `γ'` are
  have heqon : EqOn ((extChartAt I (γ t₀)) ∘ γ) ((extChartAt I (γ' t₀)) ∘ γ')
    (Ioo (t₀ - ε) (t₀ + ε)) := by
    -- uniqueness of ODE solutions in an open interval
    apply ODE_solution_unique_of_mem_set_Ioo hlip (t₀ := t₀)
      (Real.ball_eq_Ioo _ _ ▸ (Metric.mem_ball_self hε)) hcont _ hmem hcont' _ hmem' (by simp [h])
    · intros t ht
      rw [hv']
      have := hmfd.hasDerivAt ht (hsrc t ht)
      apply this.congr_deriv
      have : γ t = (extChartAt I (γ t₀)).symm (((extChartAt I (γ t₀)) ∘ γ) t) := by
        rw [Function.comp_apply, PartialEquiv.left_inv]
        exact hsrc t ht
      rw [this]
    · intros t ht
      rw [hv', h]
      have := hmfd'.hasDerivAt ht (hsrc' t ht)
      apply this.congr_deriv
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
        isIntegralCurveAt_eqOn_of_contMDiffAt (hip _ ht₁.2) hv.contMDiffAt
          (hγ.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
          (hγ'.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
          ht₁.1
      refine ⟨Ioo (max a (t₁ - ε)) (min b (t₁ + ε)),
        subset_inter
          (fun t ht => @heqon t <| mem_of_mem_of_subset ht <| Ioo_subset_Ioo (by simp) (by simp))
          (Ioo_subset_Ioo (by simp) (by simp)),
        isOpen_Ioo, ?_⟩
      rw [mem_Ioo]
      exact ⟨max_lt ht₁.2.1 (by simp [hε]), lt_min ht₁.2.2 (by simp [hε])⟩
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
  exact isIntegralCurveOn_Ioo_eqOn_of_contMDiff
    (Real.ball_eq_Ioo t₀ T ▸ Metric.mem_ball_self hT) (fun t _ => hip t) hv
    (IsIntegralCurveOn.mono (hγ.isIntegralCurveOn _) (subset_univ _))
    (IsIntegralCurveOn.mono (hγ'.isIntegralCurveOn _) (subset_univ _)) h ht
