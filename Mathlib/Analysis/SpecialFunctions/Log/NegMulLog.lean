/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Convex.Deriv

/-!
# The function `x ↦ - x * log x`

The purpose of this file is to record basic analytic properties of the function `x ↦ - x * log x`,
which is notably used in the theory of Shannon entropy.

## Main definitions

* `negMulLog`: the function `x ↦ - x * log x` from `ℝ` to `ℝ`.

-/

open scoped Topology

namespace Real

lemma continuous_mul_log : Continuous fun x ↦ x * log x := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain hx | rfl := ne_or_eq x 0
  · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [ContinuousAt, zero_mul]
  simp_rw [mul_comm _ (log _)]
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by ext; simp [em]
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [nhdsWithin_singleton, sup_le_iff, Filter.nonpos_iff, Filter.tendsto_sup]
  refine ⟨⟨tendsto_log_mul_self_nhds_zero_left, ?_⟩, ?_⟩
  · simpa only [rpow_one] using tendsto_log_mul_rpow_nhds_zero zero_lt_one
  · convert tendsto_pure_nhds (fun x ↦ log x * x) 0
    simp

lemma differentiableOn_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma hasDerivAt_mul_log {x : ℝ} (hx : x ≠ 0) : HasDerivAt (fun x ↦ x * log x) (log x + 1) x := by
  rw [← deriv_mul_log hx, hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_mul_log ?_
  simp [hx]

lemma deriv2_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_add_const, deriv_log x]
  filter_upwards [eventually_ne_nhds hx] with y hy using deriv_mul_log hy

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

lemma mul_log_nonpos {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) : x * log x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hx₀ (log_nonpos hx₀ hx₁)

section negMulLog

/-- The function `x ↦ - x * log x` from `ℝ` to `ℝ`. -/
noncomputable def negMulLog (x : ℝ) : ℝ := - x * log x

lemma negMulLog_def : negMulLog = fun x ↦ - x * log x := rfl

lemma negMulLog_eq_neg : negMulLog = fun x ↦ - (x * log x) := by simp [negMulLog_def]

@[simp] lemma negMulLog_zero : negMulLog (0 : ℝ) = 0 := by simp [negMulLog]

@[simp] lemma negMulLog_one : negMulLog (1 : ℝ) = 0 := by simp [negMulLog]

lemma negMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negMulLog x := by
  simpa only [negMulLog_eq_neg, neg_nonneg] using mul_log_nonpos h1 h2

lemma negMulLog_mul (x y : ℝ) : negMulLog (x * y) = y * negMulLog x + x * negMulLog y := by
  simp only [negMulLog, neg_mul, neg_add_rev]
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [log_mul hx hy]
  ring

lemma continuous_negMulLog : Continuous negMulLog := by
  simpa only [negMulLog_eq_neg] using continuous_mul_log.neg

lemma differentiableOn_negMulLog : DifferentiableOn ℝ negMulLog {0}ᶜ := by
  simpa only [negMulLog_eq_neg] using differentiableOn_mul_log.neg

lemma deriv_negMulLog {x : ℝ} (hx : x ≠ 0) : deriv negMulLog x = - log x - 1 := by
  rw [negMulLog_eq_neg, deriv.neg, deriv_mul_log hx]
  ring

lemma hasDerivAt_negMulLog {x : ℝ} (hx : x ≠ 0) : HasDerivAt negMulLog (- log x - 1) x := by
  rw [← deriv_negMulLog hx, hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]

lemma deriv2_negMulLog {x : ℝ} (hx : x ≠ 0) : deriv^[2] negMulLog x = - x⁻¹ := by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log hx
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
    Function.comp_apply, deriv.neg', differentiableAt_id', differentiableAt_log_iff, ne_eq] at h ⊢
  rw [h]

lemma strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog := by
  simpa only [negMulLog_eq_neg] using strictConvexOn_mul_log.neg

lemma concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog :=
  strictConcaveOn_negMulLog.concaveOn

end negMulLog

end Real
