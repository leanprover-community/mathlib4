/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Uniqueness principle for complex-differentiable functions

Unique continuation of complex-differentiable functions, and consequences.
-/

noncomputable section
universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

open Topology Set

/-- The *identity principle* for complex-differentiable functions: If a complex-differentiable
function vanishes in a whole neighborhood of a point `z₀`, then it is uniformly zero along a
connected set. Also known as *unique continuation* of complex-differentiable functions. -/
theorem DifferentiableOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : E → F} {U : Set E}
    (hf : DifferentiableOn ℂ f U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ ∈ U)
    (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  sorry

/-- Let `W` be an open set in a complex normed space `E`, and let `f` and `g` be holomorphic
functions on `W` with `f * g ≡ 0` on `W`. Let `x` be a point in `W`.  Then either `f` or `g` is zero
in a neighbourhood of `x`. -/
theorem eventually_zero_or_eventually_zero_of_mul_eq_zero {W : Set E} (hW : IsOpen W)
    {f g : E → ℂ} (hf : DifferentiableOn ℂ f W) (hg : DifferentiableOn ℂ g W)
    (H : ∀ x ∈ W, f x * g x = 0) {a : E} (ha : a ∈ W) :
    (∀ᶠ x in 𝓝 a, f x = 0) ∨ ∀ᶠ x in 𝓝 a, g x = 0 := by
  -- In either case we will prove the "eventually" by proving the result on the connected component
  -- of `W` containing `a`. We record the properties of this connected component.
  simp only [eventually_nhds_iff]
  have haW : connectedComponentIn W a ⊆ W := connectedComponentIn_subset W a
  have haW' : IsOpen (connectedComponentIn W a) := hW.connectedComponentIn
  have haW'' : a ∈ connectedComponentIn W a := mem_connectedComponentIn ha
  by_cases H : ∀ x ∈ connectedComponentIn W a, f x = 0
  · -- If `f` vanishes on the connected component, then we are done.
    left
    exact ⟨connectedComponentIn W a, H, haW', haW''⟩
  · right
    refine ⟨connectedComponentIn W a, ?_, haW', haW''⟩
    -- Otherwise there is some `b` in the connected component of `a` at which `f` does not vanish
    push_neg at H
    obtain ⟨b, hbWa, hbf⟩ := H
    have hbW : W ∈ 𝓝 b := hW.mem_nhds (haW hbWa)
    -- By continuity, actually `f` is nonvanishing on a neighbourhood of `f`
    have hbf' : ∀ᶠ x in 𝓝 b, f x ≠ 0 := (hf.continuousOn.continuousAt hbW).eventually_ne hbf
    -- Since `f * g ≡ 0`. `g` vanishes throughout this neighbourhood.
    have hbf' : ∀ᶠ x in 𝓝 b, g x = 0 := by
      filter_upwards [hbf', (hbW : ∀ᶠ x in 𝓝 b, x ∈ W)] with x hxf hxW
      exact (eq_zero_or_eq_zero_of_mul_eq_zero (H x hxW)).resolve_left hxf
    -- So by unique continuation, `g` vanishes on the whole connected component.
    rw [← isConnected_connectedComponentIn_iff] at ha
    exact (hg.mono haW).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_connectedComponentIn hbWa hbf'
