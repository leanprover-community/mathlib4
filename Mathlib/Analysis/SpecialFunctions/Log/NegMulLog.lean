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

-- TODO Maybe replace by shorter argument or put in different file?
lemma abs_min_lt_of_nonneg {α : Type} [LinearOrderedAddCommGroup α] {L R x : α}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (Llx : L < x) :
    |min L R| < x := by
  by_cases xlt : L < R
  · rw [min_eq_left_of_lt xlt, abs_eq_self.mpr hL]
    exact Llx
  · simp only [min_eq_right, le_of_not_lt xlt]
    rw [abs_eq_self.mpr hR]
    exact lt_of_le_of_lt (le_of_not_lt xlt) Llx

-- helper lemma for `not_eventually_bounded_zero_mul_log`
-- Is using `protected` good here? Probably nobody will ever want to use this?
-- Should it be inlined?
protected lemma NegMulLog.one_lt_log_sub_const_of_lt_exp_sub
    (x D : ℝ) (hx : 0 < x) (h : x < rexp (D - 2)) :
    1 < |x.log - D| := by
  by_cases abs_eq : x.log - D < 0
  · rw [abs_of_neg]
    have : x.log - D < -2 := sub_left_lt_of_lt_add ((log_lt_iff_lt_exp hx).mpr h)
    linarith
    exact abs_eq
  · have h := log_lt_log hx h
    simp only [log_exp] at h
    rw [abs_of_pos (by linarith)]
    linarith

lemma not_eventually_bounded_derivative_zero_mul_log (D : ℝ) :
    ¬ ∀ᶠ (x : ℝ) in 𝓝 0, |x * x.log - x * D| ≤ |x| := by
  simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
  intro x hx
  exists min (2⁻¹ * x) (exp (D - 2))
  have xhalf_gt0 : 0 < 2⁻¹ * x := by norm_num [hx]
  constructor
  · exact abs_min_lt_of_nonneg (le_of_lt xhalf_gt0) (exp_nonneg (D - 2)) (by norm_num; linarith)
  · have exists_pos : 0 < |min (2⁻¹ * x) (rexp (D - 2))| := by
      simp only [one_div, abs_pos]
      exact ne_of_gt (lt_min xhalf_gt0 (exp_pos (D - 2)))
    simp only [← mul_sub, one_div, abs_mul]
    apply (lt_mul_iff_one_lt_right exists_pos).mpr
    by_cases min_l : (2⁻¹ * x) < (rexp (D - 2))
    · rw [min_eq_left_of_lt min_l]
      exact NegMulLog.one_lt_log_sub_const_of_lt_exp_sub (2⁻¹ * x) D xhalf_gt0 min_l
    · simp only [min_eq_right (le_of_not_lt min_l), log_exp, sub_sub_cancel_left, abs_neg,
        Nat.abs_ofNat, Nat.one_lt_ofNat]

/- In the hypothesis, D stands for a hypothetical derivative `deriv f x0`. -/
lemma not_DifferentiableAt_of_not_eventuallly_bounded_derivative (f : ℝ → ℝ) (x0 : ℝ)
    (hf : ∀ D, ¬ ∀ᶠ (x : ℝ) in 𝓝 0, |f (x0 + x) - f x0 - x * D| ≤ |x|) :
    ¬ DifferentiableAt ℝ f x0 := by
  intro h
  have := hasDerivAt_iff_isLittleO_nhds_zero.mp (DifferentiableAt.hasDerivAt h)
  simp only [zero_add, log_zero, mul_zero, sub_zero, smul_eq_mul] at this
  have := Asymptotics.IsLittleO.bound this
  simp only [norm_mul, norm_eq_abs] at this
  have := @this 1 (by norm_num)
  simp only [one_mul] at this
  have := hf (deriv f x0)
  contradiction

lemma not_DifferentiableAt_log_mul_zero :
    ¬ DifferentiableAt ℝ (fun x ↦ x * log x) 0 := by
  apply not_DifferentiableAt_of_not_eventuallly_bounded_derivative (fun x ↦ x * log x) 0
  simp only [zero_add, log_zero, mul_zero, sub_zero]
  exact not_eventually_bounded_derivative_zero_mul_log

/-- Not differentiable, hence `deriv` has junk value zero. -/
lemma deriv_mul_log_zero : deriv (fun x ↦ x * log x) 0 = 0 :=
  deriv_zero_of_not_differentiableAt not_DifferentiableAt_log_mul_zero

open Filter in
lemma tendsto_deriv_mul_log_nhdsWithin_zero :
    Tendsto (deriv (fun x ↦ x * log x)) (𝓝[>] 0) atBot := by
  have : (deriv (fun x ↦ x * log x)) =ᶠ[𝓝[>] 0] (fun x ↦ log x + 1) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    rw [deriv_mul_log]
    simp only [Set.mem_Ioi, ne_eq]
    exact ne_of_gt hx
  simp only [tendsto_congr' this, tendsto_atBot_add_const_right, tendsto_log_nhdsWithin_zero_right]

lemma not_continuousAt_deriv_mul_log_zero :
    ¬ ContinuousAt (deriv (fun (x : ℝ) ↦ x * log x)) 0 := fun h ↦
  not_tendsto_nhds_of_tendsto_atBot tendsto_deriv_mul_log_nhdsWithin_zero _
    (h.tendsto.mono_left inf_le_left)

lemma deriv2_mul_log {x : ℝ} : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  by_cases hx : x ≠ 0
  · suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
      refine (Filter.EventuallyEq.deriv_eq this).trans ?_
      rw [deriv_add_const, deriv_log x]
    filter_upwards [eventually_ne_nhds hx] with y hy using deriv_mul_log hy
  · rw [show x = 0 by simp_all only [ne_eq, Decidable.not_not], inv_zero]
    exact deriv_zero_of_not_differentiableAt
      (fun h ↦ not_continuousAt_deriv_mul_log_zero (DifferentiableAt.continuousAt h))

lemma strictConvexOn_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_mul_log]
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

lemma differentiableAt_negMulLog_iff {x : ℝ} : DifferentiableAt ℝ negMulLog x ↔ x ≠ 0 := by
  constructor
  · unfold negMulLog
    intro h eq0
    simp only [neg_mul, differentiableAt_neg_iff, eq0] at h
    exact not_DifferentiableAt_log_mul_zero h
  · intro hx
    have : x ∈ ({0} : Set ℝ)ᶜ := by
      simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true]
    have := differentiableOn_negMulLog x this
    apply DifferentiableWithinAt.differentiableAt (s := {0}ᶜ)
    <;> simp_all only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff, not_false_eq_true,
        compl_singleton_mem_nhds_iff]

lemma deriv_negMulLog {x : ℝ} (hx : x ≠ 0) : deriv negMulLog x = - log x - 1 := by
  rw [negMulLog_eq_neg, deriv.neg, deriv_mul_log hx]
  ring

lemma hasDerivAt_negMulLog {x : ℝ} (hx : x ≠ 0) : HasDerivAt negMulLog (- log x - 1) x := by
  rw [← deriv_negMulLog hx, hasDerivAt_deriv_iff]
  refine DifferentiableOn.differentiableAt differentiableOn_negMulLog ?_
  simp [hx]

lemma deriv2_negMulLog {x : ℝ} : deriv^[2] negMulLog x = - x⁻¹ := by
  rw [negMulLog_eq_neg]
  have h := deriv2_mul_log (x := x)
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
    Function.comp_apply, deriv.neg', differentiableAt_id', differentiableAt_log_iff, ne_eq] at h ⊢
  rw [h]

lemma strictConcaveOn_negMulLog : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog := by
  simpa only [negMulLog_eq_neg] using strictConvexOn_mul_log.neg

lemma concaveOn_negMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negMulLog :=
  strictConcaveOn_negMulLog.concaveOn

end negMulLog

end Real
