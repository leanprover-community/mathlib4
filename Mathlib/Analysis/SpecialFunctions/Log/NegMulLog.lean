/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The functions `x ↦ x * log x` and `x ↦ - x * log x`

The purpose of this file is to record basic analytic properties of the functions
$$x \to \pm x * \log x$$, for use in the theory of Shannon entropy.

## TODO

Define `NegMulLog := x ↦ - x * log x` and state its properties.

-/

open scoped Topology

namespace Real

lemma tendsto_log_mul_nhds_zero_left :
    Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (- (fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Pi.neg_apply, Function.comp_apply, log_abs]
    rw [abs_of_nonpos hx.le]
    simp only [mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  rw [← neg_zero]
  refine Filter.Tendsto.neg ?_
  simp only [neg_zero]
  refine h.comp ?_
  refine tendsto_abs_nhdsWithin_zero.mono_left ?_
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  simp only [Set.mem_Iio] at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]

lemma continuous_mul_log : Continuous fun x ↦ x * log x := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  swap; · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [hx]
  rw [ContinuousAt, zero_mul]
  suffices Filter.Tendsto (fun x ↦ log x * x) (𝓝 0) (𝓝 0) by
    exact this.congr (fun x ↦ by rw [mul_comm])
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by ext; simp [em]
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [nhdsWithin_singleton, sup_le_iff, Filter.nonpos_iff, Filter.tendsto_sup]
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h' : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := tendsto_log_mul_nhds_zero_left
  refine ⟨⟨h', h⟩, ?_⟩ -- ⊢ Filter.Tendsto (fun x ↦ log x * x) (pure 0) (𝓝 0)
  rw [Filter.tendsto_pure_left, mul_zero]
  intro s hs
  obtain ⟨t, hts, _, h_zero_mem⟩ := mem_nhds_iff.mp hs
  exact hts h_zero_mem

lemma differentiableOn_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma deriv2_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_add_const, deriv_log x]
  suffices ∀ᶠ y in (𝓝 x), y ≠ 0 by
    filter_upwards [this] with y hy
    exact deriv_mul_log hy
  exact eventually_ne_nhds hx

lemma strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log hx.ne']
  positivity

lemma convexOn_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) :=
  strictConvexOn_mul_log.convexOn

lemma mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

end Real
