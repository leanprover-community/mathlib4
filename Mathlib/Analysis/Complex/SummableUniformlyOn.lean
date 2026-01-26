import Mathlib.Analysis.Calculus.FDeriv.Defs

/-!
# Differentiability of uniformly convergent series sums of functions

We collect some results about the differentiability of infinite sums.

-/

public section

lemma SummableLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ι → ℂ → E} {s : Set ℂ}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn f s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    DifferentiableOn ℂ (fun z ↦ ∑' n, f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha ↦ (hf2 a r hr).differentiableWithinAt
