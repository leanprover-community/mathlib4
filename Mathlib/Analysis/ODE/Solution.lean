/-
Copyright (c) 2024 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Topology.MetricSpace.Contracting

-- remember to fix copyright

/-!
Attempt to unify `Gronwall` and `PicardLindelof` and prepare for `LocalFlow`

Strategy:
* Define new structure `ODESolution v t₀ s x₀` which contains local solutions to the vector field
  `v`.
* Show that under certain conditions, `ODESolution v t₀ s x₀` is equivalent to satisfying an
  integral equation.
* All properties of solutions will be proved using `ODESolution`, rather than extracting `f` from
  `v` every time. <-- this is the key motivation
* Initially, we keep using coercion from `PicardLindelofData` to `ℝ → E → E`, but at some point we
  restrict ourselves to `C^p` vector fields

To consider:
* Time-independent `ODESolution`? Show equivalence?
* Not strictly a generalisation of `PicardLindelof` in cases of closed intervals (how to reconcile?)

-/

open Function Metric Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
equivalent integral equation
remark p.67
-/
noncomputable def iterateIntegral (f : ℝ → E → E) (α : ℝ → E) (t₀ : ℝ) (x₀ : E) : ℝ → E :=
  fun t ↦ x₀ + ∫ τ in t₀..t, f τ (α τ)

@[simp]
lemma iterateIntegral_apply {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ} {x₀ : E} {t : ℝ} :
    iterateIntegral f α t₀ x₀ t = x₀ + ∫ τ in t₀..t, f τ (α τ) := rfl

-- `fun t ↦ f t (α t)` is continuous if `f` and `α` are continuous
lemma continuousOn_Ioo {E : Type*} [TopologicalSpace E] {f : ℝ → E → E} {α : ℝ → E} {u : Set E}
    {s : Set ℝ}
    (hf : ContinuousOn (uncurry f) (s ×ˢ u))
    (hα : ContinuousOn α s)
    (hmem : ∀ t ∈ s, α t ∈ u) :
    ContinuousOn (fun t ↦ f t (α t)) s := by
  have : (fun t ↦ f t (α t)) = (uncurry f) ∘ fun t ↦ (t, α t) := rfl
  rw [this]
  apply hf.comp <| continuousOn_id.prod hα
  intro t ht
  exact ⟨ht, hmem t ht⟩

-- the integral equation has derivative `fun t ↦ f t (α t)`
lemma hasDerivAt_iterateIntegral [CompleteSpace E] (f : ℝ → E → E) (α : ℝ → E) {u : Set E}
    {tmin tmax t₀ : ℝ}
    -- (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u)) -- relax to continuity only?
    (hf : ContinuousOn (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    HasDerivAt (iterateIntegral f α t₀ x₀) (f t (α t)) t := by
  unfold iterateIntegral
  apply HasDerivAt.const_add
  apply intervalIntegral.integral_hasDerivAt_right -- need `CompleteSpace E`
  · apply ContinuousOn.intervalIntegrable
    apply continuousOn_Ioo hf hα hmem |>.mono
    by_cases h : t < t₀
    · rw [uIcc_of_gt h]
      exact Icc_subset_Ioo ht.1 ht₀.2
    · rw [uIcc_of_le (not_lt.mp h)]
      exact Icc_subset_Ioo ht₀.1 ht.2
  · exact continuousOn_Ioo hf hα hmem |>.stronglyMeasurableAtFilter isOpen_Ioo _ ht
  · exact continuousOn_Ioo hf hα hmem |>.continuousAt <| Ioo_mem_nhds ht.1 ht.2

-- the integral equation transfers smoothness class from `f` to `α`
lemma contDiffOn_iterateIntegral (f : ℝ → E → E) (α : ℝ → E) {u : Set E} {tmin tmax t₀ : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n (uncurry f) ((Ioo tmin tmax) ×ˢ u))
    (ht₀ : t₀ ∈ Ioo tmin tmax) (hα : ContinuousOn α (Ioo tmin tmax))
    (hmem : ∀ t ∈ Ioo tmin tmax, α t ∈ u) (x₀ : E) (hu : u ∈ 𝓝 x₀)
    (heqon : ∀ t ∈ Ioo tmin tmax, α t = iterateIntegral f α t₀ x₀ t)
    {t : ℝ} (ht : t ∈ Ioo tmin tmax) :
    ContDiffOn ℝ n α (Ioo tmin tmax) := by
  sorry

/-
prop 1.1 existence of local flow

J : open interval of ℝ containing 0
  `Ioo tmin tmax` containing 0 (generalise to `t₀`?)
U : open in banach space E containing x₀
  `u ∈ 𝓝 x₀`
  but here this is implied by `closedBall x₀ (3 * a) ⊆ u`
  why `0 < a < 1`?
f : J × U → E continuous, K-lipschitz
  `f : ℝ → E → E` with `ContinuousOn (uncurry f) (J × U)`,
  `∀ t ∈ J, LipschitzOnWith (f t) u K`
a : ℝ so that `closedBall x₀ (3 * a) ⊆ u`
b : ℝ so that eventually we get integral curve α : Ioo (- b)
α : α_x (t) is the integral curve starting at x
  `α : E → ℝ → E` with `α x t` meaning `α x` is an integral curve starting at `x`
-/

-- K is NNReal because of LipschitzOnWith
-- prop 1.1 is stated strangely at the end
theorem exist_localFlow {tmin tmax L a b : ℝ} {u : Set E} {x₀ : E} (hu : closedBall x₀ (3 * a) ⊆ u)
    {f : ℝ → E → E} {K : ℝ≥0} (hb : 0 < b)
    (hcont₁ : ∀ x ∈ u, ContinuousOn (f · x) (Ioo tmin tmax))
    (hcont₂ : ∀ t ∈ Ioo tmin tmax, ContinuousOn (f t) u)
    (hle : ∀ t ∈ Ioo tmin tmax, ∀ x ∈ u, ‖f t x‖ ≤ L)
    (hlip : ∀ t ∈ Ioo tmin tmax, LipschitzOnWith K (f t) u)
    (hlt : b * L * K < a) :
  ∃ α : E → ℝ → E, ∀ x ∈ closedBall x₀ a, α x 0 = x ∧
    ∀ t ∈ Ioo (-b) b, α x t ∈ u ∧ HasDerivAt (α x) (f t (α x t)) t := sorry

-- regularity
