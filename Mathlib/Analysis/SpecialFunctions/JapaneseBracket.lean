/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Layercake

#align_import analysis.special_functions.japanese_bracket from "leanprover-community/mathlib"@"fd5edc43dc4f10b85abfe544b88f82cf13c5f844"

/-!
# Japanese Bracket

In this file, we show that Japanese bracket $(1 + \|x\|^2)^{1/2}$ can be estimated from above
and below by $1 + \|x\|$.
The functions $(1 + \|x\|^2)^{-r/2}$ and $(1 + |x|)^{-r}$ are integrable provided that `r` is larger
than the dimension.

## Main statements

* `integrable_one_add_norm`: the function $(1 + |x|)^{-r}$ is integrable
* `integrable_jap` the Japanese bracket is integrable

-/


noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220
open scoped BigOperators NNReal Filter Topology ENNReal

open Asymptotics Filter Set Real MeasureTheory FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E]

theorem sqrt_one_add_norm_sq_le (x : E) : Real.sqrt ((1 : ℝ) + ‖x‖ ^ 2) ≤ 1 + ‖x‖ := by
  rw [sqrt_le_left (by positivity)]
  -- ⊢ 1 + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2
  simp [add_sq]
  -- 🎉 no goals
#align sqrt_one_add_norm_sq_le sqrt_one_add_norm_sq_le

theorem one_add_norm_le_sqrt_two_mul_sqrt (x : E) :
    (1 : ℝ) + ‖x‖ ≤ Real.sqrt 2 * sqrt ((1 : ℝ) + ‖x‖ ^ 2) := by
  rw [← sqrt_mul zero_le_two]
  -- ⊢ 1 + ‖x‖ ≤ sqrt (2 * (1 + ‖x‖ ^ 2))
  have := sq_nonneg (‖x‖ - 1)
  -- ⊢ 1 + ‖x‖ ≤ sqrt (2 * (1 + ‖x‖ ^ 2))
  apply le_sqrt_of_sq_le
  -- ⊢ (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2)
  linarith
  -- 🎉 no goals
#align one_add_norm_le_sqrt_two_mul_sqrt one_add_norm_le_sqrt_two_mul_sqrt

theorem rpow_neg_one_add_norm_sq_le {r : ℝ} (x : E) (hr : 0 < r) :
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2) ≤ (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) :=
  calc
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2)
      = (2 : ℝ) ^ (r / 2) * ((Real.sqrt 2 * Real.sqrt ((1 : ℝ) + ‖x‖ ^ 2)) ^ r)⁻¹ := by
      rw [rpow_div_two_eq_sqrt, rpow_div_two_eq_sqrt, mul_rpow, mul_inv, rpow_neg,
        mul_inv_cancel_left₀] <;> positivity
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
    _ ≤ (2 : ℝ) ^ (r / 2) * ((1 + ‖x‖) ^ r)⁻¹ := by
      gcongr
      -- ⊢ 1 + ‖x‖ ≤ sqrt 2 * sqrt (1 + ‖x‖ ^ 2)
      apply one_add_norm_le_sqrt_two_mul_sqrt
      -- 🎉 no goals
    _ = (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) := by rw [rpow_neg]; positivity
                                                   -- ⊢ 0 ≤ 1 + ‖x‖
                                                                  -- 🎉 no goals
#align rpow_neg_one_add_norm_sq_le rpow_neg_one_add_norm_sq_le

theorem le_rpow_one_add_norm_iff_norm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : E) :
    t ≤ (1 + ‖x‖) ^ (-r) ↔ ‖x‖ ≤ t ^ (-r⁻¹) - 1 := by
  rw [le_sub_iff_add_le', neg_inv]
  -- ⊢ t ≤ (1 + ‖x‖) ^ (-r) ↔ 1 + ‖x‖ ≤ t ^ (-r)⁻¹
  exact (Real.le_rpow_inv_iff_of_neg (by positivity) ht (neg_lt_zero.mpr hr)).symm
  -- 🎉 no goals
#align le_rpow_one_add_norm_iff_norm_le le_rpow_one_add_norm_iff_norm_le

variable (E)

theorem closedBall_rpow_sub_one_eq_empty_aux {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
    Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1) = ∅ := by
  rw [Metric.closedBall_eq_empty, sub_neg]
  -- ⊢ t ^ (-r⁻¹) < 1
  exact Real.rpow_lt_one_of_one_lt_of_neg ht (by simp only [hr, Right.neg_neg_iff, inv_pos])
  -- 🎉 no goals
#align closed_ball_rpow_sub_one_eq_empty_aux closedBall_rpow_sub_one_eq_empty_aux

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {E}

theorem finite_integral_rpow_sub_one_pow_aux {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
    (∫⁻ x : ℝ in Ioc 0 1, ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n)) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt n.cast_nonneg hnr
  -- ⊢ ∫⁻ (x : ℝ) in Ioc 0 1, ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n) < ⊤
  have h_int : ∀ x : ℝ, x ∈ Ioc (0 : ℝ) 1 →
      ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n) ≤ ENNReal.ofReal (x ^ (-(r⁻¹ * n))) := fun x hx ↦ by
    apply ENNReal.ofReal_le_ofReal
    rw [← neg_mul, rpow_mul hx.1.le, rpow_nat_cast]
    refine' pow_le_pow_of_le_left _ (by simp only [sub_le_self_iff, zero_le_one]) n
    rw [le_sub_iff_add_le', add_zero]
    refine' Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 _
    rw [Right.neg_nonpos_iff, inv_nonneg]
    exact hr.le
  refine' lt_of_le_of_lt (set_lintegral_mono' measurableSet_Ioc h_int) _
  -- ⊢ ∫⁻ (x : ℝ) in Ioc 0 1, ENNReal.ofReal (x ^ (-(r⁻¹ * ↑n))) < ⊤
  refine' IntegrableOn.set_lintegral_lt_top _
  -- ⊢ IntegrableOn (fun x => x ^ (-(r⁻¹ * ↑n))) (Ioc 0 1)
  rw [← intervalIntegrable_iff_integrable_Ioc_of_le zero_le_one]
  -- ⊢ IntervalIntegrable (fun x => x ^ (-(r⁻¹ * ↑n))) volume 0 1
  apply intervalIntegral.intervalIntegrable_rpow'
  -- ⊢ -1 < -(r⁻¹ * ↑n)
  rwa [neg_lt_neg_iff, inv_mul_lt_iff' hr, one_mul]
  -- 🎉 no goals
#align finite_integral_rpow_sub_one_pow_aux finite_integral_rpow_sub_one_pow_aux

theorem finite_integral_one_add_norm [MeasureSpace E] [BorelSpace E]
    [(volume : Measure E).IsAddHaarMeasure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    (∫⁻ x : E, ENNReal.ofReal ((1 + ‖x‖) ^ (-r))) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  -- ⊢ ∫⁻ (x : E), ENNReal.ofReal ((1 + ‖x‖) ^ (-r)) < ⊤
  -- We start by applying the layer cake formula
  have h_meas : Measurable fun ω : E => (1 + ‖ω‖) ^ (-r) :=
    -- porting note: was `by measurability`
    (measurable_norm.const_add _).pow_const _
  have h_pos : ∀ x : E, 0 ≤ (1 + ‖x‖) ^ (-r) := fun x ↦ by positivity
  -- ⊢ ∫⁻ (x : E), ENNReal.ofReal ((1 + ‖x‖) ^ (-r)) < ⊤
  rw [lintegral_eq_lintegral_meas_le volume h_pos h_meas]
  -- ⊢ ∫⁻ (t : ℝ) in Ioi 0, ↑↑volume {a | t ≤ (1 + ‖a‖) ^ (-r)} < ⊤
  have h_int : ∀ t, 0 < t → volume {a : E | t ≤ (1 + ‖a‖) ^ (-r)} =
      volume (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1)) := fun t ht ↦ by
    congr 1
    ext x
    simp only [mem_setOf_eq, mem_closedBall_zero_iff]
    exact le_rpow_one_add_norm_iff_norm_le hr (mem_Ioi.mp ht) x
  rw [set_lintegral_congr_fun measurableSet_Ioi (eventually_of_forall h_int)]
  -- ⊢ ∫⁻ (x : ℝ) in Ioi 0, ↑↑volume (Metric.closedBall 0 (x ^ (-r⁻¹) - 1)) < ⊤
  set f := fun t : ℝ ↦ volume (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1))
  -- ⊢ lintegral (Measure.restrict volume (Ioi 0)) f < ⊤
  set mB := volume (Metric.ball (0 : E) 1)
  -- ⊢ lintegral (Measure.restrict volume (Ioi 0)) f < ⊤
  -- the next two inequalities are in fact equalities but we don't need that
  calc
    ∫⁻ t in Ioi 0, f t ≤ ∫⁻ t in Ioc 0 1 ∪ Ioi 1, f t := lintegral_mono_set Ioi_subset_Ioc_union_Ioi
    _ ≤ (∫⁻ t in Ioc 0 1, f t) + ∫⁻ t in Ioi 1, f t := lintegral_union_le _ _ _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · -- We use estimates from auxiliary lemmas to deal with integral from `0` to `1`
    have h_int' : ∀ t ∈ Ioc (0 : ℝ) 1,
        f t = ENNReal.ofReal ((t ^ (-r⁻¹) - 1) ^ finrank ℝ E) * mB := fun t ht ↦ by
      refine' volume.addHaar_closedBall (0 : E) _
      rw [sub_nonneg]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by simp [hr.le])
    rw [set_lintegral_congr_fun measurableSet_Ioc (ae_of_all _ h_int'),
      lintegral_mul_const' _ _ measure_ball_lt_top.ne]
    exact ENNReal.mul_lt_top
      (finite_integral_rpow_sub_one_pow_aux (finrank ℝ E) hnr).ne measure_ball_lt_top.ne
  · -- The integral from 1 to ∞ is zero:
    have h_int'' : ∀ t ∈ Ioi (1 : ℝ), f t = 0 := fun t ht => by
      simp only [closedBall_rpow_sub_one_eq_empty_aux E hr ht, measure_empty]
    -- The integral over the constant zero function is finite:
    rw [set_lintegral_congr_fun measurableSet_Ioi (ae_of_all volume <| h_int''), lintegral_const 0,
      zero_mul]
    exact WithTop.zero_lt_top
    -- 🎉 no goals
#align finite_integral_one_add_norm finite_integral_one_add_norm

theorem integrable_one_add_norm [MeasureSpace E] [BorelSpace E] [(@volume E _).IsAddHaarMeasure]
    {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) : Integrable fun x : E => (1 + ‖x‖) ^ (-r) := by
  constructor
  -- ⊢ AEStronglyMeasurable (fun x => (1 + ‖x‖) ^ (-r)) volume
  · -- porting note: was `measurability`
    exact ((measurable_norm.const_add _).pow_const _).aestronglyMeasurable
    -- 🎉 no goals
  -- Lower Lebesgue integral
  have : (∫⁻ a : E, ‖(1 + ‖a‖) ^ (-r)‖₊) = ∫⁻ a : E, ENNReal.ofReal ((1 + ‖a‖) ^ (-r)) :=
    lintegral_nnnorm_eq_of_nonneg fun _ => rpow_nonneg_of_nonneg (by positivity) _
  rw [HasFiniteIntegral, this]
  -- ⊢ ∫⁻ (a : E), ENNReal.ofReal ((1 + ‖a‖) ^ (-r)) < ⊤
  exact finite_integral_one_add_norm hnr
  -- 🎉 no goals
#align integrable_one_add_norm integrable_one_add_norm

theorem integrable_rpow_neg_one_add_norm_sq [MeasureSpace E] [BorelSpace E]
    [(@volume E _).IsAddHaarMeasure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    Integrable fun x : E => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2) := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  -- ⊢ Integrable fun x => (1 + ‖x‖ ^ 2) ^ (-r / 2)
  refine ((integrable_one_add_norm hnr).const_mul <| (2 : ℝ) ^ (r / 2)).mono'
    ?_ (eventually_of_forall fun x => ?_)
  · -- porting note: was `measurability`
    exact (((measurable_id.norm.pow_const _).const_add _).pow_const _).aestronglyMeasurable
    -- 🎉 no goals
  refine (abs_of_pos ?_).trans_le (rpow_neg_one_add_norm_sq_le x hr)
  -- ⊢ 0 < (1 + ‖x‖ ^ 2) ^ (-r / 2)
  positivity
  -- 🎉 no goals
#align integrable_rpow_neg_one_add_norm_sq integrable_rpow_neg_one_add_norm_sq
