/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
module

public import Mathlib.Analysis.Normed.Order.UpperLower
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are null-measurable.
Recall that `x ≤ y` iff `∀ i, x i ≤ y i`, and `s` is order-connected iff
`∀ x y ∈ s, ∀ z, x ≤ z → z ≤ y → z ∈ s`.

## Main declarations

* `Set.OrdConnected.null_frontier`: The frontier of an order-connected set in `ℝⁿ` has measure `0`.

## Notes

We prove null-measurability in `ℝⁿ` with the `∞`-metric, but this transfers directly to `ℝⁿ` with
the Euclidean metric because they have the same measurable sets.

Null-measurability can't be strengthened to measurability because any antichain (and in particular
any subset of the antidiagonal `{(x, y) | x + y = 0}`) is order-connected.

## Sketch proof

1. To show an order-connected set is null-measurable, it is enough to show it has null frontier.
2. Since an order-connected set is the intersection of its upper and lower closure, it's enough to
  show that upper and lower sets have null frontier.
3. WLOG let's prove it for an upper set `s`.
4. By the Lebesgue density theorem, it is enough to show that any frontier point `x` of `s` is not a
  Lebesgue point, namely we want the density of `s` over small balls centered at `x` to not tend to
  either `0` or `1`.
5. This is true, since by the upper setness of `s` we can intercalate a ball of radius `δ / 4` in
  `s` intersected with the upper quadrant of the ball of radius `δ` centered at `x` (recall that the
  balls are taken in the ∞-norm, so they are cubes), and another ball of radius `δ / 4` in `sᶜ` and
  the lower quadrant of the ball of radius `δ` centered at `x`.

## TODO

Generalize so that it also applies to `ℝ × ℝ`, for example.
-/
set_option backward.defeqAttrib.useBackward true

public section

open Filter MeasureTheory Metric Set
open scoped Topology

variable {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)} {x : ι → ℝ}

/-- If we can fit a small ball inside a set `s` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `0`.

Along with `aux₁`, this proves that `x` is not a Lebesgue point of `s`. This will be used to prove
that the frontier of an order-connected set is null. -/
private lemma aux₀
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 0) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
    (Frequently.of_forall fun _ ↦ lt_irrefl <| ENNReal.ofReal <| 4⁻¹ ^ Fintype.card ι)
    ((Filter.Tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds ?_).mono fun n ↦
      lt_of_le_of_lt ?_)
  on_goal 2 =>
    calc
      ENNReal.ofReal (4⁻¹ ^ Fintype.card ι)
        = volume (closedBall (f (ε n) (hε' n)) (ε n / 4)) / volume (closedBall x (ε n)) := ?_
      _ ≤ volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n)) := by
        gcongr
        exact subset_inter ((hf₁ _ <| hε' n).trans interior_subset_closure) <| hf₀ _ <| hε' n
    have := hε' n
    rw [Real.volume_pi_closedBall, Real.volume_pi_closedBall, ← ENNReal.ofReal_div_of_pos,
      ← div_pow, mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals positivity

/-- If we can fit a small ball inside a set `sᶜ` intersected with any neighborhood of `x`, then the
density of `s` near `x` is not `1`.

Along with `aux₀`, this proves that `x` is not a Lebesgue point of `s`. This will be used to prove
that the frontier of an order-connected set is null. -/
private lemma aux₁
    (h : ∀ δ, 0 < δ →
      ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior sᶜ) :
    ¬Tendsto (fun r ↦ volume (closure s ∩ closedBall x r) / volume (closedBall x r)) (𝓝[>] 0)
        (𝓝 1) := by
  choose f hf₀ hf₁ using h
  intro H
  obtain ⟨ε, -, hε', hε₀⟩ := exists_seq_strictAnti_tendsto_nhdsWithin (0 : ℝ)
  refine not_eventually.2
      (Frequently.of_forall fun _ ↦ lt_irrefl <| 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι))
      ((Filter.Tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) <|
            ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero ?_).mono
        fun n ↦ lt_of_le_of_lt' ?_)
  on_goal 2 =>
    calc
      volume (closure s ∩ closedBall x (ε n)) / volume (closedBall x (ε n))
        ≤ volume (closedBall x (ε n) \ closedBall (f (ε n) <| hε' n) (ε n / 4)) /
          volume (closedBall x (ε n)) := by
        gcongr
        rw [diff_eq_compl_inter]
        refine inter_subset_inter_left _ ?_
        rw [subset_compl_comm, ← interior_compl]
        exact hf₁ _ _
      _ = 1 - ENNReal.ofReal (4⁻¹ ^ Fintype.card ι) := ?_
    dsimp only
    have := hε' n
    rw [measure_diff (hf₀ _ _) _ ((Real.volume_pi_closedBall _ _).trans_ne ENNReal.ofReal_ne_top),
      Real.volume_pi_closedBall, Real.volume_pi_closedBall, ENNReal.sub_div fun _ _ ↦ _,
      ENNReal.div_self _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_div_of_pos, ← div_pow,
      mul_div_mul_left _ _ (two_ne_zero' ℝ), div_right_comm, div_self, one_div]
  all_goals try positivity
  · simp_all
  · exact measurableSet_closedBall.nullMeasurableSet

theorem IsUpperSet.null_frontier (hs : IsUpperSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_setOf, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx

theorem IsLowerSet.null_frontier (hs : IsLowerSet s) : volume (frontier s) = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_)
    (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet _
      (isClosed_closure (s := s)).measurableSet)
  by_cases h : x ∈ closure s <;>
    simp only [mem_compl_iff, mem_setOf, h, not_false_eq_true, indicator_of_notMem,
      indicator_of_mem, Pi.one_apply]
  · refine aux₁ fun _ ↦ hs.compl.exists_subset_ball <| frontier_subset_closure ?_
    rwa [frontier_compl]
  · exact aux₀ fun _ ↦ hs.exists_subset_ball <| frontier_subset_closure hx

theorem Set.OrdConnected.null_frontier (hs : s.OrdConnected) : volume (frontier s) = 0 := by
  rw [← hs.upperClosure_inter_lowerClosure]
  exact measure_mono_null (frontier_inter_subset _ _) <| measure_union_null
    (measure_inter_null_of_null_left _ (UpperSet.upper _).null_frontier)
    (measure_inter_null_of_null_right _ (LowerSet.lower _).null_frontier)

protected theorem Set.OrdConnected.nullMeasurableSet (hs : s.OrdConnected) : NullMeasurableSet s :=
  nullMeasurableSet_of_null_frontier hs.null_frontier

theorem IsAntichain.volume_eq_zero [Nonempty ι] (hs : IsAntichain (· ≤ ·) s) : volume s = 0 := by
  refine measure_mono_null ?_ hs.ordConnected.null_frontier
  rw [← closure_diff_interior, hs.interior_eq_empty, diff_empty]
  exact subset_closure
