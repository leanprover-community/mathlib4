/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of uniformly convergent series sums of functions

We collect some results about the differentiability of infinite sums.

-/

lemma SummableLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn (fun n ↦ ((fun z ↦ f n z))) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    DifferentiableOn ℂ (fun z ↦ ∑' n , f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha ↦ (hf2 a r hr).differentiableWithinAt
