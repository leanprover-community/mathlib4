/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The positive tangent cone and curves

In this file we provide a characterization of the positive tangent cone in terms of the derivative
of curves.

-/

@[expose] public section

open Filter Set Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x y y' : E}

/-- If a curve `γ` is fully contained in a set `s` for all positive times and `γ 0 = x`, then
the derivative of `γ` at `0` is contained in the positive tangent cone. -/
lemma HasDerivWithinAt.mem_posTangentConeAt {γ : ℝ → E} (h_cont : ContinuousOn γ (Set.Ici 0))
    (h_diff : HasDerivWithinAt γ y (Set.Ici 0) 0) (h₀ : γ 0 = x) (hs : ∀ t > 0, γ t ∈ s) :
    y ∈ posTangentConeAt s x := by
  apply mem_tangentConeAt_of_seq (𝓝[>] (0 : ℝ)) (·⁻¹ |>.toNNReal) (γ · - γ 0)
  · suffices Tendsto (γ · - γ 0) (𝓝[≥] 0) (𝓝 0) from
      this.mono_left <| nhdsWithin_mono 0 (by simp)
    simpa using (h_cont 0 (by simp)).tendsto.sub (tendsto_const_nhds (x := γ 0))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa [h₀] using hs t ht
  · rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at h_diff
    apply h_diff.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by simp [ht.le])]
    simp [slope]

/-- If a curve `γ` is fully contained in a set `s` for all positive times and `γ 0 = x`, then
the derivative of `γ` at `0` is contained in the positive tangent cone. -/
lemma HasDerivAt.mem_posTangentConeAt {γ : ℝ → E} (hc : Continuous γ)
    (hd : HasDerivAt γ y 0) (h0 : γ 0 = x) (hs : ∀ t > 0, γ t ∈ s) :
    y ∈ posTangentConeAt s x :=
  hd.hasDerivWithinAt.mem_posTangentConeAt hc.continuousOn h0 hs
