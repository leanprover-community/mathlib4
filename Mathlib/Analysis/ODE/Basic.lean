/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Integral curves of vector fields on a Banach space

Let `E` be a Banach space and `v : E → E` be a vector field on `E`. An integral curve of `v` is a
function `γ : ℝ → E` such that the derivative of `γ` at `t` equals `v t (γ t)`. The integral curve
may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : E → E` be a vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsIntegralCurveOn γ v s` and `IsIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `IsIntegralCurveOn γ v s` means `γ t` is tangent to `v (γ t)` within `s` for all `t ∈ s`. The
value of `γ` outside of `s` is irrelevant and considered junk. -/
def IsIntegralCurveOn (γ : ℝ → E) (v : E → E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivWithinAt γ (v (γ t)) s t

/-- `IsIntegralCurveAt γ v t₀` means `γ : ℝ → E` is a local integral curve of `v` in a neighbourhood
containing `t₀`. The value of `γ` outside of this neighbourhood is irrelevant and considered
junk. -/
def IsIntegralCurveAt (γ : ℝ → E) (v : E → E) (t₀ : ℝ) : Prop :=
  ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v (γ t)) t

/-- `IsIntegralCurve γ v` means `γ : ℝ → E` is a global integral curve of `v`. That is, `γ t` is
tangent to `v (γ t)` for all `t : ℝ`. -/
def IsIntegralCurve (γ : ℝ → E) (v : E → E) : Prop :=
  ∀ t : ℝ, HasDerivAt γ (v (γ t)) t

variable {γ γ' : ℝ → E} {v : E → E} {s s' : Set ℝ} {t₀ : ℝ}

lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set ℝ) :
    IsIntegralCurveOn γ v s := fun t _ ↦ (h t).hasDerivWithinAt

lemma isIntegralCurve_iff_isIntegralCurveOn :
    IsIntegralCurve γ v ↔ IsIntegralCurveOn γ v univ :=
  ⟨fun h ↦ h.isIntegralCurveOn _, fun h t ↦ (h t (mem_univ _)).hasDerivAt Filter.univ_mem⟩

lemma isIntegralCurveAt_iff :
    IsIntegralCurveAt γ v t₀ ↔ ∃ s ∈ 𝓝 t₀, IsIntegralCurveOn γ v s := by
  constructor
  · intro h
    rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht ↦ (h t ht).hasDerivWithinAt⟩
  · intro h
    rw [IsIntegralCurveAt, Filter.eventually_iff_exists_mem]
    obtain ⟨s, hs, h⟩ := h
    rw [mem_nhds_iff] at hs
    obtain ⟨s', h1, h2, h3⟩ := hs
    refine ⟨s', h2.mem_nhds h3, ?_⟩
    intro t ht
    apply (h t (h1 ht)).hasDerivAt
    rw [mem_nhds_iff]
    exact ⟨s', h1, h2, ht⟩

/-- `γ` is an integral curve for `v` at `t₀` iff `γ` is an integral curve on some interval
containing `t₀`. -/
lemma isIntegralCurveAt_iff' :
    IsIntegralCurveAt γ v t₀ ↔ ∃ ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [isIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, ?_⟩
    intro t ht
    exact (h t (hε' ht)).mono hε'
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : ℝ) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ ↦ (h t).hasDerivWithinAt⟩

lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ ∀ t : ℝ, IsIntegralCurveAt γ v t :=
  ⟨fun h ↦ h.isIntegralCurveAt, fun h t ↦ by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff.mp (h t)
    exact h t (mem_of_mem_nhds hs) |>.hasDerivAt hs⟩

lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' ⊆ s) :
    IsIntegralCurveOn γ v s' := fun t ht ↦ (h t (hs ht)).mono hs

lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff.mp h
  h t₀ (mem_of_mem_nhds hs) |>.hasDerivAt hs

lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s ∈ 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/-- If `γ` is an integral curve at each `t ∈ s`, it is an integral curve on `s`. -/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : ∀ t ∈ s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  apply HasDerivAt.hasDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')

lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ ∀ t ∈ s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht ↦ h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ ∈ s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt

lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht ↦ (hγ t ht).continuousWithinAt

lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff.mp hγ
  hγ.continuousWithinAt (mem_of_mem_nhds hs) |>.continuousAt hs

lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t ↦ (hγ.isIntegralCurveAt t).continuousAt
