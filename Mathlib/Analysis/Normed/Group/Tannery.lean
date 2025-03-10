/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Tannery's theorem

Tannery's theorem gives a sufficient criterion for the limit of an infinite sum (with respect to
an auxiliary parameter) to equal the sum of the pointwise limits. See
https://en.wikipedia.org/wiki/Tannery%27s_theorem. It is a special case of the dominated convergence
theorem (with the measure chosen to be the counting measure); but we give here a direct proof, in
order to avoid some unnecessary hypotheses that appear when specialising the general
measure-theoretic result.
-/

open Filter Topology

/-- **Tannery's theorem**: topological sums commute with termwise limits, when the norms of the
summands are eventually uniformly bounded by a summable function.

(This is the special case of the Lebesgue dominated convergence theorem for the counting measure
on a discrete set. However, we prove it under somewhat weaker assumptions than the general
measure-theoretic result, e.g. `G` is not assumed to be an `ℝ`-vector space or second countable,
and the limit is along an arbitrary filter rather than `atTop ℕ`.)

See also:
* `MeasureTheory.tendsto_integral_of_dominated_convergence` (for general integrals, but
  with more assumptions on `G`)
* `continuous_tsum` (continuity of infinite sums in a parameter)
-/
lemma tendsto_tsum_of_dominated_convergence {α β G : Type*} {𝓕 : Filter α}
    [NormedAddCommGroup G] [CompleteSpace G]
    {f : α → β → G} {g : β → G} {bound : β → ℝ} (h_sum : Summable bound)
    (hab : ∀ k : β, Tendsto (f · k) 𝓕 (𝓝 (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (∑' k, f · k) 𝓕 (𝓝 (∑' k, g k)) := by
  -- WLOG β is nonempty
  rcases isEmpty_or_nonempty β
  · simpa only [tsum_empty] using tendsto_const_nhds
  -- WLOG 𝓕 ≠ ⊥
  rcases 𝓕.eq_or_neBot with rfl | _
  · simp only [tendsto_bot]
  -- Auxiliary lemmas
  have h_g_le (k : β) : ‖g k‖ ≤ bound k :=
    le_of_tendsto (tendsto_norm.comp (hab k)) <| h_bound.mono (fun n h => h k)
  have h_sumg : Summable (‖g ·‖) :=
    h_sum.of_norm_bounded _ (fun k ↦ (norm_norm (g k)).symm ▸ h_g_le k)
  have h_suma : ∀ᶠ n in 𝓕, Summable (‖f n ·‖) := by
    filter_upwards [h_bound] with n h
    exact h_sum.of_norm_bounded _ <| by simpa only [norm_norm] using h
  -- Now main proof, by an `ε / 3` argument
  rw [Metric.tendsto_nhds]
  intro ε hε
  let ⟨S, hS⟩ := h_sum
  obtain ⟨T, hT⟩ : ∃ (T : Finset β), dist (∑ b ∈ T, bound b) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    classical exact Eventually.exists <| hS _ (by positivity)
  have h1 : ∑' (k : (Tᶜ : Set β)), bound k < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set β)), bound k‖ := Real.le_norm_self _
         _ = ‖S - ∑ b ∈ T, bound b‖          := congrArg _ ?_
         _ < ε / 3                            := by rwa [dist_eq_norm, norm_sub_rev] at hT
    simpa only [sum_add_tsum_compl h_sum, eq_sub_iff_add_eq'] using hS.tsum_eq
  have h2 : Tendsto (∑ k ∈ T, f · k) 𝓕 (𝓝 (T.sum g)) := tendsto_finset_sum _ (fun i _ ↦ hab i)
  rw [Metric.tendsto_nhds] at h2
  filter_upwards [h2 (ε / 3) (by positivity), h_suma, h_bound] with n hn h_suma h_bound
  rw [dist_eq_norm, ← tsum_sub h_suma.of_norm h_sumg.of_norm,
    ← sum_add_tsum_compl (s := T) (h_suma.of_norm.sub h_sumg.of_norm),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hn
  · rw [tsum_sub (h_suma.subtype _).of_norm (h_sumg.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (h_suma.subtype _)).trans ?_).trans_lt h1
      exact tsum_le_tsum (h_bound ·) (h_suma.subtype _) (h_sum.subtype _)
    · refine ((norm_tsum_le_tsum_norm <| h_sumg.subtype _).trans ?_).trans_lt h1
      exact tsum_le_tsum (h_g_le ·) (h_sumg.subtype _) (h_sum.subtype _)
