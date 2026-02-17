/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Integral curves of vector fields on a normed vector space

Let `E` be a normed vector space and `v : ℝ → E → E` be a time-dependent vector field on `E`.
An integral curve  of `v` is a function `γ : ℝ → E` such that the derivative of `γ` at `t` equals
`v t (γ t)`. The integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : ℝ → E → E` be a time-dependent vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v t (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v t (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v t (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v t (γ t)` within `s` for all `t ∈ s`. -/
def IsIntegralCurveOn (γ : ℝ → E) (v : ℝ → E → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (v t (γ t)) s t

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. -/
def IsIntegralCurveAt (γ : ℝ → E) (v : ℝ → E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

/-- `IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That is, `γ t` is
tangent to `v t (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → E) (v : ℝ → E → E) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (v t (γ t)) t

variable {γ γ' : ℝ → E} {v : ℝ → E → E} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ (h t).hasDerivWithinAt

lemma isIntegralCurveOn_univ :
    IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v :=
  ⟨fun h t ↦ (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h ↦ h.isIntegralCurveOn _⟩

lemma isIntegralCurveAt_iff_exists_mem_nhds :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ ↦ ⟨s, hs, fun t ht ↦ (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt, Metric.eventually_nhds_iff_ball]
  constructor
  · rintro ⟨ε, hε, hγ⟩
    exact ⟨ε, hε, fun t ht ↦ (hγ t ht).hasDerivWithinAt⟩
  · rintro ⟨ε, hε, hγ⟩
    exact ⟨ε, hε, fun t ht ↦ (hγ t ht).hasDerivAt (Metric.isOpen_ball.mem_nhds ht)⟩

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasDerivWithinAt⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasDerivAt hs⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ h t (hs ht) |>.mono hs

lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v t₀ (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasDerivAt hs

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs') |>.hasDerivWithinAt

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt

lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := (hγ · · |>.continuousWithinAt)

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)
