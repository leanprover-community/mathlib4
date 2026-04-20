/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

This is the first of a series of files, organised as follows:
* `Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean` (this file): Basic definitions and lemmas
  relating them to each other and to continuity and differentiability
* `Mathlib/Geometry/Manifold/IntegralCurve/Transform.lean`: Lemmas about translating or scaling the
  domain of an integral curve by a constant
* `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`: Local existence and uniqueness
  theorems for integral curves

## Main definitions

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
* `IsMIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsMIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsMIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsMIntegralCurveOn γ v s` and `IsMIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## TODO

* Implement `IsMIntegralCurveWithinAt`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If `γ : ℝ → M` is $C^1$ on `s : Set ℝ` and `v` is a vector field on `M`,
`IsMIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` for all `t ∈ s`. The value of `γ`
outside of `s` is irrelevant and considered junk. -/
def IsMIntegralCurveOn (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasMFDerivAt[s] γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v` is a vector field on `M` and `t₀ : ℝ`, `IsMIntegralCurveAt γ v t₀` means `γ : ℝ → M` is a
local integral curve of `v` in a neighbourhood containing `t₀`. The value of `γ` outside of this
interval is irrelevant and considered junk. -/
def IsMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v : M → TM` is a vector field on `M`, `IsMIntegralCurve γ v` means `γ : ℝ → M` is a global
integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
@[informal "integral curves"]
def IsMIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) : Prop :=
  ∀ t : ℝ, HasMFDerivAt% γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsMIntegralCurve.isMIntegralCurveOn (h : IsMIntegralCurve γ v) (s : Set ℝ) :
    IsMIntegralCurveOn γ v s := fun t _ ↦ (h t).hasMFDerivWithinAt

lemma isMIntegralCurve_iff_isMIntegralCurveOn :
    IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isMIntegralCurveOn _, fun h t ↦ (h t (mem_univ _)).hasMFDerivAt Filter.univ_mem⟩

lemma isMIntegralCurveAt_iff :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsMIntegralCurveOn γ v s := by
  constructor
  · intro h
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht ↦ (h t ht).hasMFDerivWithinAt⟩
  · rintro ⟨s, hs, h⟩
    rw [IsMIntegralCurveAt, Filter.eventually_iff_exists_mem]
    obtain ⟨s', h1, h2, h3⟩ := mem_nhds_iff.mp hs
    refine ⟨s', h2.mem_nhds h3, ?_⟩
    intro t ht
    apply (h t (h1 ht)).hasMFDerivAt
    rw [mem_nhds_iff]
    exact ⟨s', h1, h2, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isMIntegralCurveAt_iff' :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [isMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, fun t ht ↦ (h t (hε' ht)).mono hε'⟩
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

lemma IsMIntegralCurve.isMIntegralCurveAt (h : IsMIntegralCurve γ v) (t : ℝ) :
    IsMIntegralCurveAt γ v t :=
  isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasMFDerivWithinAt⟩

lemma isMIntegralCurve_iff_isMIntegralCurveAt :
    IsMIntegralCurve γ v ↔ ∀ t : ℝ, IsMIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isMIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasMFDerivAt hs⟩

lemma IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsMIntegralCurveOn γ v s' := fun t ht ↦ (h t (hs ht)).mono hs

lemma IsMIntegralCurveAt.hasMFDerivAt (h : IsMIntegralCurveAt γ v t₀) :
    HasMFDerivAt% γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasMFDerivAt hs

lemma IsMIntegralCurveOn.isMIntegralCurveAt (h : IsMIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsMIntegralCurveAt γ v t₀ := isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsMIntegralCurveAt.isMIntegralCurveOn (h : ∀ t ∈ s, IsMIntegralCurveAt γ v t) :
    IsMIntegralCurveOn γ v s := by
  intro t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')

lemma isMIntegralCurveOn_iff_isMIntegralCurveAt (hs : IsOpen s) :
    IsMIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsMIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩

lemma IsMIntegralCurveOn.continuousWithinAt (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).1

lemma IsMIntegralCurveOn.continuousOn (hγ : IsMIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).continuousWithinAt

lemma IsMIntegralCurveAt.continuousAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs

lemma IsMIntegralCurve.continuous (hγ : IsMIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t ↦ (hγ.isMIntegralCurveAt t).continuousAt

variable [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
/-- If `γ` is an integral curve of a vector field `v`, then `γ t` is tangent to `v (γ t)` when
expressed in the local chart around the initial point `γ t₀`. -/
lemma IsMIntegralCurveOn.hasDerivWithinAt (hγ : IsMIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivWithinAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) s t := by
  -- turn `HasDerivWithinAt` into comp of `HasMFDerivWithinAt`
  replace hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma IsMIntegralCurveAt.eventually_hasDerivAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ∀ᶠ t in 𝓝 t₀, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  apply eventually_mem_nhds_iff.mpr
    (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _)) |>.and hγ |>.mono
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage, extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) ht2).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl
