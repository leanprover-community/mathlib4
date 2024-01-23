/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Geometry.Manifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsIntegralCurveOn γ v s` and `IsIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## Main results

* `exists_isIntegralCurveAt_of_contMDiffAt_boundaryless`: Existence of local integral curves for a
$C^1$ vector field. This follows from the existence theorem for solutions to ODEs
(`exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt`).

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a TODO.

We state simpler versions of the theorem for boundaryless manifolds as corollaries.

## TODO

* The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
J. M. Lee. May require submanifolds.

## Tags

integral curve, vector field, local existence
-/

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [SmoothManifoldWithCorners I M]

/-- If `γ : ℝ → M` is $C^1$ on `s : Set ℝ` and `v` is a vector field on `M`,
`IsIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. The value of `γ`
outside of `s` is irrelevant and considered junk. -/
def IsIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v` is a vector field on `M` and `t₀ : ℝ`, `IsIntegralCurveAt γ v t₀` means `γ : ℝ → M` is a
local integral curve of `v` in a neighbourhood containing `t₀`. The value of `γ` outside of this
interval is irrelevant and considered junk. -/
def IsIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v : M → TM` is a vector field on `M`, `IsIntegralCurve γ v` means `γ : ℝ → M` is a global
integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) : Prop :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ h t

lemma isIntegralCurve_iff_isIntegralCurveOn : IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isIntegralCurveOn _, fun h t ↦ h t (mem_univ _)⟩

lemma isIntegralCurveAt_iff :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  simp_rw [IsIntegralCurveOn, ← Filter.eventually_iff_exists_mem, IsIntegralCurveAt]

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isIntegralCurveAt_iff' :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  simp_rw [IsIntegralCurveOn, ← Metric.eventually_nhds_iff_ball, IsIntegralCurveAt]

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t := isIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ h t⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs)⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (mem_of_mem_of_subset ht hs)

lemma IsIntegralCurveOn.of_union (h : IsIntegralCurveOn γ v s) (h' : IsIntegralCurveOn γ v s') :
    IsIntegralCurveOn γ v (s ∪ s') := fun _ ↦ fun | .inl ht => h _ ht | .inr ht => h' _ ht

lemma IsIntegralCurveAt.hasMFDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs)

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff.mp (h t ht)
  exact h t (mem_of_mem_nhds hs)

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

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
  convert hγ.comp_add (-dt)
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]
  simp

lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, dist_sub_eq_dist_add_right]

lemma isIntegralCurveAt_comp_add {dt : ℝ} :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext
  simp only [Function.comp_apply, neg_add_cancel_right]
  simp only [sub_neg_eq_add, sub_add_cancel]

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
  rw [isIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε / |a|, by positivity, ?_⟩
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

end Scaling

variable (t₀) {x₀ : M}

/-- Existence of local integral curves for a $C^1$ vector field at interior points of a smooth
manifold. -/
theorem exists_isIntegralCurveAt_of_contMDiffAt
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀)
    (hx : I.IsInteriorPoint x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ := by
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
  have hnhds : f ⁻¹' (interior (extChartAt I x₀).target) ∈ 𝓝 t₀ :=
    hcont _ (isOpen_interior.mem_nhds ((I.isInteriorPoint_iff).mp hx))
  rw [← eventually_mem_nhds] at hnhds
  -- obtain a neighbourhood `s` so that the above conditions both hold in `s`
  obtain ⟨s, hs, haux⟩ := (hf2.and hnhds).exists_mem
  -- prove that `γ := (extChartAt I x₀).symm ∘ f` is a desired integral curve
  refine ⟨(extChartAt I x₀).symm ∘ f,
    Eq.symm (by rw [Function.comp_apply, hf1, PartialEquiv.left_inv _ (mem_extChartAt_source ..)]),
    isIntegralCurveAt_iff.mpr ⟨s, hs, ?_⟩⟩
  intros t ht
  -- collect useful terms in convenient forms
  let xₜ : M := (extChartAt I x₀).symm (f t) -- `xₜ := γ t`
  have h : HasDerivAt f (x := t) <| fderivWithin ℝ (extChartAt I x₀ ∘ (extChartAt I xₜ).symm)
    (range I) (extChartAt I xₜ xₜ) (v xₜ) := (haux t ht).1
  rw [← tangentCoordChange_def] at h
  have hf3 := mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2
  have hf3' := mem_of_mem_of_subset hf3 interior_subset
  have hft1 := mem_preimage.mp <|
    mem_of_mem_of_subset hf3' (extChartAt I x₀).target_subset_preimage_source
  have hft2 := mem_extChartAt_source I xₜ
  -- express the derivative of the integral curve in the local chart
  refine ⟨(continuousAt_extChartAt_symm'' _ _ hf3').comp h.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  show HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ f) (v xₜ) t
  -- express `v (γ t)` as `D⁻¹ D (v (γ t))`, where `D` is a change of coordinates, so we can use
  -- `HasFDerivAt.comp_hasDerivAt` on `h`
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := v xₜ) hft2,
    ← tangentCoordChange_comp (x := x₀) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I x₀).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, hf3⟩
  rw [← (extChartAt I x₀).right_inv hf3']
  exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩

/-- Existence of local integral curves for a $C^1$ vector field on a smooth manifold without
boundary. -/
lemma exists_isIntegralCurveAt_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) x₀) :
    ∃ γ : ℝ → M, γ t₀ = x₀ ∧ IsIntegralCurveAt γ v t₀ :=
  exists_isIntegralCurveAt_of_contMDiffAt t₀ hv (BoundarylessManifold.isInteriorPoint I)

section Naturality

variable
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [SmoothManifoldWithCorners I' M']
  {v' : (x : M') → TangentSpace I' x}

/-- Let `v` and `v'` be vector fields on `M` and `M'`, respectively, and let `f : M → M'` be a
  differentiable map. If `v` and `v'` are `f`-related, then `f` maps integral curves of `v` to
  integral curves of `v'`. -/
lemma IsIntegralCurveAt.of_mdifferentiable_related (h : IsIntegralCurveAt γ v t₀)
    {f : M → M'} (hf : MDifferentiable I I' f) (hv : ∀ x : M, v' (f x) = mfderiv I I' f x (v x)) :
    IsIntegralCurveAt (f ∘ γ) v' t₀ := by
  apply h.mono
  intros t ht
  apply (HasMFDerivAt.comp t (hf (γ t)).hasMFDerivAt ht).congr_mfderiv
  rw [Function.comp_apply, hv, ContinuousLinearMap.comp_smulRight]

/-- Let `v` and `v'` be vector fields on `M` and `M'`, respectively, and let `f : M → M'` be a
  differentiable map. If `f` maps integral curves of `v` to integral curves of `v'`, then `v` and
  `v'` are `f`-related. -/
lemma mdifferentiable_related_of_isIntegralCurveAt [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    {f : M → M'} (hf : MDifferentiable I I' f)
    (h : ∀ (γ : ℝ → M) (t₀ : ℝ), IsIntegralCurveAt γ v t₀ → IsIntegralCurveAt (f ∘ γ) v' t₀)
    (x : M) : v' (f x) = mfderiv I I' f x (v x) := by
  obtain ⟨γ, h0, hγ⟩ : ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurveAt γ v 0 :=
    exists_isIntegralCurveAt_of_contMDiffAt_boundaryless 0 hv.contMDiffAt
  have hγ' := (h γ 0 hγ).hasMFDerivAt
  have hγ := hγ.hasMFDerivAt
  rw [Function.comp_apply, h0] at hγ'
  rw [h0] at hγ
  have := hasMFDerivAt_unique hγ' <| (hf (γ 0)).hasMFDerivAt.comp 0 hγ
  rw [ContinuousLinearMap.comp_smulRight, ContinuousLinearMap.smulRight_one_eq_iff, h0] at this
  exact this

end Naturality
