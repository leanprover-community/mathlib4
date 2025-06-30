/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

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

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

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
  ∀ t ∈ s, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v` is a vector field on `M` and `t₀ : ℝ`, `IsMIntegralCurveAt γ v t₀` means `γ : ℝ → M` is a
local integral curve of `v` in a neighbourhood containing `t₀`. The value of `γ` outside of this
interval is irrelevant and considered junk. -/
def IsMIntegralCurveAt (γ : ℝ → M) (v : (x : M) → TangentSpace I x) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight <| v (γ t))

/-- If `v : M → TM` is a vector field on `M`, `IsMIntegralCurve γ v` means `γ : ℝ → M` is a global
integral curve of `v`. That is, `γ t` is tangent to `v (γ t)` for all `t : ℝ`. -/
def IsMIntegralCurve (γ : ℝ → M) (v : (x : M) → TangentSpace I x) : Prop :=
  ∀ t : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t)))

variable {γ γ' : ℝ → M} {v : (x : M) → TangentSpace I x} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsMIntegralCurve.isMIntegralCurveOn (h : IsMIntegralCurve γ v) (s : Set ℝ) :
    IsMIntegralCurveOn γ v s := fun t _ ↦ h t

lemma isMIntegralCurve_iff_isMIntegralCurveOn :
    IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isMIntegralCurveOn _, fun h t ↦ h t (mem_univ _)⟩

lemma isMIntegralCurveAt_iff :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsMIntegralCurveOn γ v s := by
  simp_rw [IsMIntegralCurveOn, ← Filter.eventually_iff_exists_mem, IsMIntegralCurveAt]

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isMIntegralCurveAt_iff' :
    IsMIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  simp_rw [IsMIntegralCurveOn, ← Metric.eventually_nhds_iff_ball, IsMIntegralCurveAt]

lemma IsMIntegralCurve.isMIntegralCurveAt (h : IsMIntegralCurve γ v) (t : ℝ) :
    IsMIntegralCurveAt γ v t := isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ h t⟩

lemma isMIntegralCurve_iff_isMIntegralCurveAt :
    IsMIntegralCurve γ v ↔ ∀ t : ℝ, IsMIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isMIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs)⟩

lemma IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsMIntegralCurveOn γ v s' := fun t ht ↦ h t (mem_of_mem_of_subset ht hs)

lemma IsMIntegralCurveOn.of_union (h : IsMIntegralCurveOn γ v s) (h' : IsMIntegralCurveOn γ v s') :
    IsMIntegralCurveOn γ v (s ∪ s') := fun _ ↦ fun | .inl ht => h _ ht | .inr ht => h' _ ht

lemma IsMIntegralCurveAt.hasMFDerivAt (h : IsMIntegralCurveAt γ v t₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs)

lemma IsMIntegralCurveOn.isMIntegralCurveAt (h : IsMIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsMIntegralCurveAt γ v t₀ := isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsMIntegralCurveAt.isMIntegralCurveOn (h : ∀ t ∈ s, IsMIntegralCurveAt γ v t) :
    IsMIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t ht)
  exact h t (mem_of_mem_nhds hs)

lemma isMIntegralCurveOn_iff_isMIntegralCurveAt (hs : IsOpen s) :
    IsMIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsMIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩

lemma IsMIntegralCurveOn.continuousAt (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousAt γ t₀ := (hγ t₀ ht).1

lemma IsMIntegralCurveOn.continuousOn (hγ : IsMIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).1.continuousWithinAt

lemma IsMIntegralCurveAt.continuousAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
  hγ.continuousAt <| mem_of_mem_nhds hs

lemma IsMIntegralCurve.continuous (hγ : IsMIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun _ ↦ (hγ.isMIntegralCurveOn univ).continuousAt (mem_univ _)

variable [IsManifold I 1 M]

/-- If `γ` is an integral curve of a vector field `v`, then `γ t` is tangent to `v (γ t)` when
expressed in the local chart around the initial point `γ t₀`. -/
lemma IsMIntegralCurveOn.hasDerivAt (hγ : IsMIntegralCurveOn γ v s) {t : ℝ} (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I (γ t₀)).source) :
    HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  -- turn `HasDerivAt` into comp of `HasMFDerivAt`
  have hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t
    (hasMFDerivAt_extChartAt (I := I) hsrc) (hγ _ ht)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

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
