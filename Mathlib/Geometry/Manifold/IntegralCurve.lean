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
* `isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless`: Uniqueness of local integral curves for a
$C^1$ vector field. This follows from the uniqueness theorem for solutions to ODEs
(`ODE_solution_unique_of_mem_set_Ioo`). This requires the manifold to be Hausdorff (`T2Space`).

## Implementation notes

For the existence and uniqueness theorems, we assume that the image of the integral curve lies in
the interior of the manifold. The case where the integral curve may lie on the boundary of the
manifold requires special treatment, and we leave it as a TODO.

We state simpler versions of the theorem for boundaryless manifolds as corollaries.

## TODO

* The case where the integral curve may venture to the boundary of the manifold. See Theorem 9.34,
Lee. May require submanifolds.

## Reference
* Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.

## Tags

integral curve, vector field, local existence, uniqueness
-/

open scoped Manifold Topology

open Set Classical

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
  simp_rw [IsIntegralCurveOn, ← Filter.eventually_iff_exists_mem]
  rfl

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isIntegralCurveAt_iff' :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  simp_rw [IsIntegralCurveOn, ← Metric.eventually_nhds_iff_ball]
  rfl

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

lemma IsIntegralCurveOn.congr_of_eqOn (hs : IsOpen s) (h : IsIntegralCurveOn γ v s)
    (hγ : EqOn γ γ' s) : IsIntegralCurveOn γ' v s := by
  intros t ht
  rw [← hγ ht]
  apply (h t ht).congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem (hs.mem_nhds ht) hγ.symm

lemma IsIntegralCurveAt.congr_of_eventuallyEq (h : IsIntegralCurveAt γ v t₀)
    (hγ : γ =ᶠ[nhds t₀] γ') : IsIntegralCurveAt γ' v t₀ := by
  obtain ⟨s, hdrv, hs1, hs2⟩ := eventually_nhds_iff.mp (h.and hγ)
  refine eventually_nhds_iff.mpr ⟨s, fun t ht ↦ ?_, hs1, hs2⟩
  apply ((hdrv t ht).2 ▸ (hdrv t ht).1).congr_of_eventuallyEq
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨s, hs1.mem_nhds ht, fun t' ht' ↦ (hdrv t' ht').2.symm⟩

lemma IsIntegralCurve.congr (h : IsIntegralCurve γ v) (hγ : γ = γ') :
    IsIntegralCurve γ' v := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  apply h.congr_of_eqOn isOpen_univ <| (eqOn_univ γ γ').mpr hγ

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

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

lemma isIntegralCurveOn_comp_add (dt : ℝ) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· + dt)) v { t | t + dt ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  · simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [mem_setOf_eq, neg_add_cancel_right, setOf_mem_eq]

lemma isIntegralCurveOn_comp_sub (dt : ℝ) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· - dt)) v { t | t - dt ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add dt
  ext t
  · simp only [Function.comp_apply, add_sub_cancel]
  · simp only [mem_setOf_eq, add_sub_cancel, setOf_mem_eq]

-- TODO: missing lemma(s) for `Ioo`
lemma isIntegralCurveOn_Ioo_comp_add {a b : ℝ} (dt : ℝ) :
    IsIntegralCurveOn γ v (Ioo a b) ↔
      IsIntegralCurveOn (γ ∘ (· + dt)) v (Ioo (a - dt) (b - dt)) := by
  have : {t | t + dt ∈ Ioo a b} = Ioo (a - dt) (b - dt) := by
    ext t
    rw [mem_setOf, mem_Ioo, mem_Ioo, sub_lt_iff_lt_add (c := dt), lt_sub_iff_add_lt (b := dt)]
  rw [isIntegralCurveOn_comp_add dt, this]

lemma isIntegralCurveOn_Ioo_comp_sub {a b : ℝ} (dt : ℝ) :
    IsIntegralCurveOn γ v (Ioo a b) ↔
      IsIntegralCurveOn (γ ∘ (· - dt)) v (Ioo (a + dt) (b + dt)) := by
  have : {t | t - dt ∈ Ioo a b} = Ioo (a + dt) (b + dt) := by
    ext t
    rw [mem_setOf, mem_Ioo, mem_Ioo, sub_lt_iff_lt_add (c := dt), lt_sub_iff_add_lt (b := dt)]
  rw [isIntegralCurveOn_comp_sub dt, this]

lemma IsIntegralCurveAt.comp_add (hγ : IsIntegralCurveAt γ v t₀) (dt : ℝ) :
    IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  rw [isIntegralCurveAt_iff'] at *
  obtain ⟨ε, hε, h⟩ := hγ
  refine ⟨ε, hε, ?_⟩
  convert h.comp_add dt
  ext t
  rw [mem_setOf_eq, Metric.mem_ball, Metric.mem_ball, dist_sub_eq_dist_add_right]

lemma isIntegralCurveAt_comp_add (dt : ℝ) :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· + dt)) v (t₀ - dt) := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  · simp only [Function.comp_apply, neg_add_cancel_right]
  · simp only [sub_neg_eq_add, sub_add_cancel]

lemma isIntegralCurveAt_comp_sub (dt : ℝ) :
    IsIntegralCurveAt γ v t₀ ↔ IsIntegralCurveAt (γ ∘ (· - dt)) v (t₀ + dt) := by
  have := isIntegralCurveAt_comp_add (v := v) (γ := γ) (t₀ := t₀) (-dt)
  simpa

lemma IsIntegralCurve.comp_add (hγ : IsIntegralCurve γ v) (dt : ℝ) :
    IsIntegralCurve (γ ∘ (· + dt)) v := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_add _

lemma isIntegralCurve_comp_add (dt : ℝ) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· + dt)) v := by
  refine ⟨fun hγ ↦ hγ.comp_add _, fun hγ ↦ ?_⟩
  convert hγ.comp_add (-dt)
  ext t
  simp only [Function.comp_apply, neg_add_cancel_right]

lemma isIntegralCurve_comp_sub (dt : ℝ) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· - dt)) v := by
  have := isIntegralCurve_comp_add (v := v) (γ := γ) (-dt)
  simpa

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

lemma isIntegralCurveOn_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurveOn γ v s ↔ IsIntegralCurveOn (γ ∘ (· * a)) (a • v) { t | t * a ∈ s } := by
  refine ⟨fun hγ ↦ hγ.comp_mul a, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  ext t
  · simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [mem_setOf_eq, mul_assoc, inv_mul_eq_div, div_self ha, mul_one, setOf_mem_eq]

-- TODO: missing lemma(s) about Ioo
lemma isIntegralCurveOn_Ioo_comp_mul_pos {ε a : ℝ} (ha : 0 < a) :
    IsIntegralCurveOn γ v (Ioo (t₀ - ε) (t₀ + ε)) ↔
      IsIntegralCurveOn (γ ∘ (· * a)) (a • v) (Ioo ((t₀ - ε) / a) ((t₀ + ε) / a)) := by
  have : {t | t * a ∈ Ioo (t₀ - ε) (t₀ + ε)} = Ioo ((t₀ - ε) / a) ((t₀ + ε) / a) := by
    ext t
    rw [mem_setOf, mem_Ioo, mem_Ioo, div_lt_iff ha, lt_div_iff ha]
  rw [isIntegralCurveOn_comp_mul_ne_zero (ne_of_gt ha), this]

lemma isIntegralCurveOn_Ioo_comp_mul_neg {ε a : ℝ} (ha : a < 0) :
    IsIntegralCurveOn γ v (Ioo (t₀ - ε) (t₀ + ε)) ↔
      IsIntegralCurveOn (γ ∘ (· * a)) (a • v) (Ioo ((t₀ + ε) / a) ((t₀ - ε) / a)) := by
  have : {t | t * a ∈ Ioo (t₀ - ε) (t₀ + ε)} = Ioo ((t₀ + ε) / a) ((t₀ - ε) / a) := by
    ext t
    rw [mem_setOf, mem_Ioo, mem_Ioo, div_lt_iff_of_neg ha, lt_div_iff_of_neg ha, and_comm]
  rw [isIntegralCurveOn_comp_mul_ne_zero (ne_of_lt ha), this]

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
  convert hγ.comp_mul_ne_zero (inv_ne_zero ha)
  ext t
  · simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]
  · simp only [div_inv_eq_mul, div_mul_cancel _ ha]

lemma IsIntegralCurve.comp_mul (hγ : IsIntegralCurve γ v) (a : ℝ) :
    IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  rw [isIntegralCurve_iff_isIntegralCurveOn] at *
  exact hγ.comp_mul _

lemma isIntegralCurve_comp_mul_ne_zero {a : ℝ} (ha : a ≠ 0) :
    IsIntegralCurve γ v ↔ IsIntegralCurve (γ ∘ (· * a)) (a • v) := by
  refine ⟨fun hγ ↦ hγ.comp_mul _, fun hγ ↦ ?_⟩
  convert hγ.comp_mul a⁻¹
  ext t
  · simp only [Function.comp_apply, mul_assoc, inv_mul_eq_div, div_self ha, mul_one]
  · simp only [smul_smul, inv_mul_eq_div, div_self ha, one_smul]

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
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).1.continuousWithinAt

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff.mp hγ
  hγ.continuousAt <| mem_of_mem_nhds hs

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) :
    Continuous γ := continuous_iff_continuousAt.mpr
      fun _ ↦ (hγ.isIntegralCurveOn univ).continuousAt (mem_univ _)

end Scaling

/-! ### Existence and uniqueness -/

section ExistUnique

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

variable {t₀}

/-- Local integral curves are unique.

If a $C^1$ vector field `v` admits two local integral curves `γ γ' : ℝ → M` at `t₀` with
`γ t₀ = γ' t₀`, then `γ` and `γ'` agree on some open interval containing `t₀`. -/
theorem isIntegralCurveAt_eqOn_of_contMDiffAt (hγt₀ : I.IsInteriorPoint (γ t₀))
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    ∃ ε > 0, EqOn γ γ' (Ioo (t₀ - ε) (t₀ + ε)) := by
  -- first define `v'` as the vector field expressed in the local chart around `γ t₀`
  -- this is basically what the function looks like when `hv` is unfolded
  set v' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I (γ t₀)).symm x) (γ t₀) ((extChartAt I (γ t₀)).symm x)
      (v ((extChartAt I (γ t₀)).symm x)) with hv'

  -- extract a set `s` on which `v'` is Lipschitz
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  obtain ⟨K, s, hs, hlip⟩ : ∃ K, ∃ s ∈ nhds _, LipschitzOnWith K v' s :=
    (hv.contDiffAt (range_mem_nhds_isInteriorPoint hγt₀)).snd.exists_lipschitzOnWith
  have hlip (t : ℝ) : LipschitzOnWith K ((fun _ ↦ v') t) ((fun _ ↦ s) t) := hlip

  -- `γ t` when expressed in the local chart should remain inside `s`
  have hcont : ContinuousAt ((extChartAt I (γ t₀)) ∘ γ) t₀ :=
    (continuousAt_extChartAt ..).comp hγ.continuousAt
  rw [continuousAt_def] at hcont
  have hnhds := hcont _ hs
  rw [← eventually_mem_nhds] at hnhds

  -- `γ t` should remain inside the domain of the local chart around `γ t₀`
  have hsrc := continuousAt_def.mp hγ.continuousAt _ <| extChartAt_source_mem_nhds I (γ t₀)
  rw [← eventually_mem_nhds] at hsrc

  -- same as above but for `γ'`
  have hcont' : ContinuousAt ((extChartAt I (γ' t₀)) ∘ γ') t₀ :=
    ContinuousAt.comp (continuousAt_extChartAt ..) hγ'.continuousAt
  rw [continuousAt_def] at hcont'
  have hnhds' := hcont' _ (h ▸ hs)
  rw [← eventually_mem_nhds] at hnhds'

  have hsrc' := continuousAt_def.mp hγ'.continuousAt _ <| extChartAt_source_mem_nhds I (γ' t₀)
  rw [← eventually_mem_nhds] at hsrc'

  -- there exists a neighbourhood around `t₀` in which all of the above hold
  have haux := hnhds.and <| hsrc.and <| hγ.and <| hnhds'.and <| hsrc'.and hγ'
  rw [Metric.eventually_nhds_iff_ball] at haux

  obtain ⟨ε, hε, haux⟩ := haux
  refine ⟨ε, hε, ?_⟩

  -- break out all the conditions again
  have hmem := fun t ht ↦ mem_preimage.mp <| mem_of_mem_nhds (haux t ht).1
  have hsrc := fun t ht ↦ mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.1
  have hcrv : IsIntegralCurveOn _ _ _ := fun t ht ↦ (haux t ht).2.2.1
  have hmem' := fun t ht ↦ mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.2.2.1
  have hsrc' := fun t ht ↦ mem_preimage.mp <| mem_of_mem_nhds (haux t ht).2.2.2.2.1
  have hcrv' : IsIntegralCurveOn _ _ _ := fun t ht ↦ (haux t ht).2.2.2.2.2

  -- `γ` and `γ'` when expressed in the local chart are continuous on this neighbourhood
  have hcont := (continuousOn_extChartAt I (γ t₀)).comp hcrv.continuousOn hsrc
  have hcont' := (continuousOn_extChartAt I (γ' t₀)).comp hcrv'.continuousOn hsrc'

  simp_rw [Real.ball_eq_Ioo] at hmem hsrc hcrv hcont hmem' hsrc' hcrv' hcont'

  -- `γ` and `γ'` are equal on `Ioo (t₀ - ε) (t₀ + ε)` when expressed in the local chart
  have heqon : EqOn ((extChartAt I (γ t₀)) ∘ γ) ((extChartAt I (γ' t₀)) ∘ γ')
    (Ioo (t₀ - ε) (t₀ + ε)) := by
    -- uniqueness of ODE solutions in an open interval
    apply ODE_solution_unique_of_mem_set_Ioo hlip (t₀ := t₀)
      (Real.ball_eq_Ioo _ _ ▸ (Metric.mem_ball_self hε)) hcont _ hmem hcont' _ hmem' (by simp [h])
    · intros t ht
      rw [hv']
      have := hcrv.hasDerivAt ht (hsrc t ht)
      apply this.congr_deriv
      have : γ t = (extChartAt I (γ t₀)).symm (((extChartAt I (γ t₀)) ∘ γ) t) := by
        rw [Function.comp_apply, PartialEquiv.left_inv]
        exact hsrc t ht
      rw [this]
    · intros t ht
      rw [hv', h]
      have := hcrv'.hasDerivAt ht (hsrc' t ht)
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

theorem isIntegralCurveAt_eqOn_of_contMDiffAt_boundaryless [BoundarylessManifold I M]
    (hv : ContMDiffAt I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : IsIntegralCurveAt γ v t₀) (hγ' : IsIntegralCurveAt γ' v t₀) (h : γ t₀ = γ' t₀) :
    ∃ ε > 0, EqOn γ γ' (Ioo (t₀ - ε) (t₀ + ε)) :=
  isIntegralCurveAt_eqOn_of_contMDiffAt (BoundarylessManifold.isInteriorPoint I) hv hγ hγ' h

variable [T2Space M] {a b a' b' : ℝ}

/-- Integral curves are unique on open intervals.

If a $C^1$ vector field `v` admits two integral curves `γ γ' : ℝ → M` on some open interval
`Ioo a b`, and `γ t₀ = γ' t₀` for some `t ∈ Ioo a b`, then `γ` and `γ'` agree on `Ioo a b`. -/
theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff (ht₀ : t₀ ∈ Ioo a b)
    (hγt : ∀ t ∈ Ioo a b, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  -- since `Ioo a b` is connected, we get `s = Ioo a b` by showing that `s` is clopen in `Ioo a b`
  -- in the subtype toplogy (`s` is also non-empty by assumption)
  -- here we use a slightly weaker alternative theorem
  suffices hsub : Ioo a b ⊆ s from fun t ht ↦ mem_setOf.mp ((subset_def ▸ hsub) t ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · -- is this really the most convenient way to pass to subtype topology?
    -- TODO: shorten this when better API around subtype topology exists
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
      isIntegralCurveAt_eqOn_of_contMDiffAt (hγt _ ht₁.2) hv.contMDiffAt
        (hγ.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
        (hγ'.isIntegralCurveAt <| Ioo_mem_nhds ht₁.2.1 ht₁.2.2)
        ht₁.1
    refine ⟨Ioo (max a (t₁ - ε)) (min b (t₁ + ε)),
      subset_inter
        (fun t ht ↦ @heqon t <| mem_of_mem_of_subset ht <| Ioo_subset_Ioo (by simp) (by simp))
        (Ioo_subset_Ioo (by simp) (by simp)),
      isOpen_Ioo, ?_⟩
    exact ⟨max_lt ht₁.2.1 (by simp [hε]), lt_min ht₁.2.2 (by simp [hε])⟩

theorem isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (ht₀ : t₀ ∈ Ioo a b)
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurveOn γ v (Ioo a b)) (hγ' : IsIntegralCurveOn γ' v (Ioo a b))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) :=
  isIntegralCurveOn_Ioo_eqOn_of_contMDiff
    ht₀ (fun _ _ ↦ BoundarylessManifold.isInteriorPoint I) hv hγ hγ' h

/-- Global integral curves are unique.

If a continuously differentiable vector field `v` admits two global integral curves
`γ γ' : ℝ → M`, and `γ t₀ = γ' t₀` for some `t₀`, then `γ` and `γ'` are equal. -/
theorem isIntegralCurve_eq_of_contMDiff (hγt : ∀ t, I.IsInteriorPoint (γ t))
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' := by
  ext t
  obtain ⟨T, hT, ht⟩ : ∃ T > 0, t ∈ Ioo (t₀ - T) (t₀ + T) := by
    refine ⟨|t - t₀| + 1, by positivity, ?_⟩
    by_cases ht : t - t₀ < 0
    · rw [abs_of_neg ht]
      constructor <;> linarith
    · rw [abs_of_nonneg (not_lt.mp ht)]
      constructor <;> linarith
  exact isIntegralCurveOn_Ioo_eqOn_of_contMDiff
    (Real.ball_eq_Ioo t₀ T ▸ Metric.mem_ball_self hT) (fun t _ ↦ hγt t) hv
    ((hγ.isIntegralCurveOn _).mono  (subset_univ _))
    ((hγ'.isIntegralCurveOn _).mono (subset_univ _)) h ht

theorem isIntegralCurve_Ioo_eq_of_contMDiff_boundaryless [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, v x⟩ : TangentBundle I M)))
    (hγ : IsIntegralCurve γ v) (hγ' : IsIntegralCurve γ' v) (h : γ t₀ = γ' t₀) : γ = γ' :=
  isIntegralCurve_eq_of_contMDiff (fun _ ↦ BoundarylessManifold.isInteriorPoint I) hv hγ hγ' h

lemma exists_isIntegralCurveOn_Ioo_eqOn [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (h : ∀ a, ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)) {a a' : ℝ} (hpos : 0 < a')
    (hle : a' ≤ a) : EqOn (choose (h a')) (choose (h a)) (Ioo (-a') a') := by
  have ⟨h0', hγ'⟩ := choose_spec (h a')
  have ⟨h0, hγ⟩ := choose_spec (h a)
  apply isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv hγ' (hγ.mono _) (by rw [h0', h0])
  · rw [mem_Ioo]
    exact ⟨neg_lt_zero.mpr hpos, by positivity⟩
  · apply Ioo_subset_Ioo <;> linarith

/-- Suppose for every `a : ℝ`, there exists an integral curve `γ a` on `Ioo (-a) a`.
Then, the global curve `γ_ext := fun t ↦ γ (|t| + 1) t` agrees with each `γ a` on `Ioo (-a) a`.
This will help us show that `γ` is a global integral curve. -/
lemma exists_integralCurve_of_exists_isIntegralCurveOn_Ioo_eqOn_aux [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (h : ∀ a, ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)) {a : ℝ} :
    EqOn (fun t' ↦ choose (h (|t'| + 1)) t') (choose (h a)) (Ioo (-a) a) := by
  intros t' ht'
  by_cases hlt : |t'| + 1 < a
  · apply exists_isIntegralCurveOn_Ioo_eqOn hv h (by positivity) (le_of_lt hlt)
    · rw [mem_Ioo, ← abs_lt]
      exact lt_add_one _
  · apply (exists_isIntegralCurveOn_Ioo_eqOn hv h _ _ _).symm
    · have := lt_trans ht'.1 ht'.2
      rw [neg_lt_self_iff] at this
      exact this
    · exact not_lt.mp hlt
    · exact ht'

/-- If for every `a : ℝ`, there exists an integral curve defined on `Ioo (-a) a`, then there exists
  a global integral curve. -/
lemma exists_integralCurve_of_exists_isIntegralCurveOn_Ioo [BoundarylessManifold I M] [T2Space M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) {x : M}
    (h : ∀ a, ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)) :
    ∃ γ, γ 0 = x ∧ IsIntegralCurve γ v := by
  refine ⟨fun t' ↦ choose (h (|t'| + 1)) t', (choose_spec (h (|0| + 1))).1, ?_⟩
  intro t
  apply HasMFDerivAt.congr_of_eventuallyEq (f := choose (h (|t| + 1)))
  · apply (choose_spec (h (|t| + 1))).2 t
    rw [mem_Ioo, ← abs_lt]
    exact lt_add_one _
  · rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo (-(|t| + 1)) (|t| + 1), ?_,
      exists_integralCurve_of_exists_isIntegralCurveOn_Ioo_eqOn_aux hv h⟩
    · have := lt_add_of_pos_right |t| zero_lt_one
      rw [abs_lt] at this
      exact Ioo_mem_nhds this.1 this.2

lemma exists_isIntegralCurve_iff_exists_isIntegralCurveOn_Ioo [BoundarylessManifold I M] [T2Space M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M))) (x : M) :
    (∃ γ, γ 0 = x ∧ IsIntegralCurve γ v) ↔
      ∀ a, ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a) :=
  ⟨fun ⟨γ, h1, h2⟩ _ ↦ ⟨γ, h1, h2.isIntegralCurveOn _⟩,
   exists_integralCurve_of_exists_isIntegralCurveOn_Ioo hv⟩

lemma piecewise_eqOn_symm [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' v (Ioo a' b'))
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    EqOn (piecewise (Ioo a b) γ γ') γ' (Ioo a' b') := by
  intros t ht
  suffices H : EqOn γ γ' (Ioo (max a a') (min b b')) by
    by_cases hmem : t ∈ Ioo a b
    · rw [piecewise, if_pos hmem]
      apply H
      simp [ht.1, ht.2, hmem.1, hmem.2]
    · rw [piecewise, if_neg hmem]
  apply isIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless _ hv
    (hγ.mono (Ioo_subset_Ioo (le_max_left ..) (min_le_left ..)))
    (hγ'.mono (Ioo_subset_Ioo (le_max_right ..) (min_le_right ..))) h
  exact ⟨max_lt ht₀.1.1 ht₀.2.1, lt_min ht₀.1.2 ht₀.2.2⟩

/-- The extension of an integral curve by another integral curve is an integral curve.

  If two integral curves are defined on overlapping open intervals, and they agree at a point in
  their common domain, then they can be patched together to form a longer integral curve.

  This is stated for manifolds without boundary for simplicity. We actually only need to assume that
  the images of `γ` and `γ'` lie in the interior of the manifold. -/
lemma isIntegralCurveOn_piecewise [BoundarylessManifold I M]
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {a b a' b' : ℝ} (hγ : IsIntegralCurveOn γ v (Ioo a b))
    (hγ' : IsIntegralCurveOn γ' v (Ioo a' b')) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b ∩ Ioo a' b') (h : γ t₀ = γ' t₀) :
    IsIntegralCurveOn (piecewise (Ioo a b) γ γ') v (Ioo a b ∪ Ioo a' b') := by
  intros t ht
  by_cases hmem : t ∈ Ioo a b
  · rw [piecewise, if_pos hmem]
    apply (hγ t hmem).congr_of_eventuallyEq
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a b, isOpen_Ioo.mem_nhds hmem, ?_⟩
    intros t' ht'
    rw [piecewise, if_pos ht']
  · rw [mem_union, or_iff_not_imp_left] at ht
    have hmem' := ht hmem
    rw [piecewise, if_neg hmem]
    apply (hγ' t hmem').congr_of_eventuallyEq
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Ioo a' b', isOpen_Ioo.mem_nhds hmem', piecewise_eqOn_symm hv hγ hγ' ht₀ h⟩

-- move this lemma elsewhere
lemma Ioo_subset_Ioo_union_Ioo {a' b' a b c d : ℝ} (haa : a ≤ a') (hcb : c < b) (hbd : b' ≤ d) :
    Ioo a' b' ⊆ Ioo a b ∪ Ioo c d := by
  intro t
  rw [mem_Ioo, mem_union, mem_Ioo, mem_Ioo]
  rintro ⟨ha, hb⟩
  by_cases hlt : t < b
  · apply Or.inl
    exact ⟨by linarith, hlt⟩
  · apply Or.inr
    exact ⟨by linarith, by linarith⟩

/-- If there exists `ε > 0` such that the local integral curve at each point `x : M` is defined at
  least on an open interval `Ioo (-ε) ε`, then every point on `M` has a global integral
  curve passing through it.

  See Lemma 9.15, Lee -/
lemma exists_isIntegralCurve_of_isIntegralCurveOn [BoundarylessManifold I M]
    {v : (x : M) → TangentSpace I x}
    (hv : ContMDiff I I.tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle I M)))
    {ε : ℝ} (hε : 0 < ε) (h : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-ε) ε))
    (x : M) : ∃ γ : ℝ → M, γ 0 = x ∧ IsIntegralCurve γ v := by
  have hnon : Set.Nonempty {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} := ⟨ε, h x⟩
  by_cases hbdd : BddAbove {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)}
  · set asup := sSup {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} with hasup
    -- we will obtain two integral curves, one centred at some `t₀ > 0` with
    -- `0 ≤ asup - ε < t₀ < asup`; let `t₀ = asup - ε / 2`
    -- another centred at 0 with domain up to `a ∈ S` with `t₀ < a < asup`
    obtain ⟨a, ha, hlt⟩ := Real.add_neg_lt_sSup hnon (ε := - (ε / 2))
      (by rw [neg_lt, neg_zero]; exact half_pos hε)
    have hale : a ≤ asup := le_csSup hbdd ha
    rw [mem_setOf] at ha
    rw [← hasup, ← sub_eq_add_neg] at hlt

    have hεle : ε ≤ asup := le_csSup hbdd (h x)

    -- integral curve defined on `Ioo (-a) a`
    obtain ⟨γ, h0, hγ⟩ := ha
    -- integral curve starting at `-(asup - ε / 2)` with radius `ε`
    obtain ⟨γ1_aux, h1_aux, hγ1⟩ := h (γ (-(asup - ε / 2)))
    rw [isIntegralCurveOn_Ioo_comp_add (asup - ε / 2)] at hγ1
    let γ1 := γ1_aux ∘ (· + (asup - ε / 2))
    have heq1 : γ1 (-(asup - ε / 2)) = γ (-(asup - ε / 2)) := by simp [h1_aux]
    -- integral curve starting at `asup - ε / 2` with radius `ε`
    obtain ⟨γ2_aux, h2_aux, hγ2⟩ := h (γ (asup - ε / 2))
    rw [isIntegralCurveOn_Ioo_comp_sub (asup - ε / 2)] at hγ2
    let γ2 := γ2_aux ∘ (· - (asup - ε / 2))
    have heq2 : γ2 (asup - ε / 2) = γ (asup - ε / 2) := by simp [h2_aux]

    -- extend `γ` on the left by `γ1` and on the right by `γ2`
    set γ_ext : ℝ → M := piecewise (Ioo (-(asup + ε / 2)) a)
      (piecewise (Ioo (-a) a) γ γ1) γ2 with γ_ext_def
    have hext : IsIntegralCurveOn γ_ext v (Ioo (-(asup + ε / 2)) (asup + ε / 2)) := by
      apply (isIntegralCurveOn_piecewise (t₀ := asup - ε / 2) hv _ hγ2
        (by refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith) _).mono
          (Ioo_subset_Ioo_union_Ioo le_rfl (by linarith) (by linarith))
      apply (isIntegralCurveOn_piecewise (t₀ := -(asup - ε / 2)) hv hγ hγ1
        (by refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith) heq1.symm).mono
      · rw [union_comm (Ioo (-a) a)]
        apply Ioo_subset_Ioo_union_Ioo (by linarith) (by linarith) le_rfl
      · rw [piecewise, if_pos ⟨by linarith, by linarith⟩, ← heq2]
    have hmem : asup + ε / 2 ∈ {a | ∃ γ, γ 0 = x ∧ IsIntegralCurveOn γ v (Ioo (-a) a)} := by
      refine ⟨γ_ext, ?_, hext⟩
      rw [γ_ext_def, piecewise, if_pos ⟨by linarith, by linarith⟩, piecewise,
        if_pos ⟨by linarith, by linarith⟩]
      exact h0
    absurd lt_add_of_pos_right asup (half_pos hε)
    rw [not_lt]
    exact le_csSup hbdd hmem
  · rw [not_bddAbove_iff] at hbdd
    simp_rw [mem_setOf] at hbdd
    rw [exists_isIntegralCurve_iff_exists_isIntegralCurveOn_Ioo hv]
    intro a
    obtain ⟨⟨γ, hγ1, hγ2⟩, hlt⟩ := choose_spec (hbdd a)
    refine ⟨γ, hγ1, hγ2.mono ?_⟩
    apply Ioo_subset_Ioo <;>
    simp [le_of_lt hlt]

end ExistUnique
