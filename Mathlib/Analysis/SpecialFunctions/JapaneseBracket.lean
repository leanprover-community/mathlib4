/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.special_functions.japanese_bracket
! leanprover-community/mathlib commit fd5edc43dc4f10b85abfe544b88f82cf13c5f844
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Layercake

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

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220
open scoped BigOperators NNReal Filter Topology ENNReal

open Asymptotics Filter Set Real MeasureTheory FiniteDimensional

variable {E : Type _} [NormedAddCommGroup E]

theorem sqrt_one_add_norm_sq_le (x : E) : Real.sqrt ((1 : ℝ) + ‖x‖ ^ 2) ≤ 1 + ‖x‖ := by
  rw [sqrt_le_left (by positivity)]
  simp [add_sq]
#align sqrt_one_add_norm_sq_le sqrt_one_add_norm_sq_le

theorem one_add_norm_le_sqrt_two_mul_sqrt (x : E) :
    (1 : ℝ) + ‖x‖ ≤ Real.sqrt 2 * sqrt ((1 : ℝ) + ‖x‖ ^ 2) := by
  rw [← sqrt_mul zero_le_two]
  have := sq_nonneg (‖x‖ - 1)
  apply le_sqrt_of_sq_le
  linarith
#align one_add_norm_le_sqrt_two_mul_sqrt one_add_norm_le_sqrt_two_mul_sqrt

theorem rpow_neg_one_add_norm_sq_le {r : ℝ} (x : E) (hr : 0 < r) :
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2) ≤ (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) :=
  calc
    ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2)
      = (2 : ℝ) ^ (r / 2) * ((Real.sqrt 2 * Real.sqrt ((1 : ℝ) + ‖x‖ ^ 2)) ^ r)⁻¹ := by
      rw [rpow_div_two_eq_sqrt, rpow_div_two_eq_sqrt, mul_rpow, mul_inv, rpow_neg,
        mul_inv_cancel_left₀] <;> positivity
    _ ≤ (2 : ℝ) ^ (r / 2) * ((1 + ‖x‖) ^ r)⁻¹ := by
      gcongr
      apply one_add_norm_le_sqrt_two_mul_sqrt
    _ = (2 : ℝ) ^ (r / 2) * (1 + ‖x‖) ^ (-r) := by rw [rpow_neg]; positivity
#align rpow_neg_one_add_norm_sq_le rpow_neg_one_add_norm_sq_le

theorem le_rpow_one_add_norm_iff_norm_le {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : E) :
    t ≤ (1 + ‖x‖) ^ (-r) ↔ ‖x‖ ≤ t ^ (-r⁻¹) - 1 := by
  rw [le_sub_iff_add_le', neg_inv]
  exact (Real.le_rpow_inv_iff_of_neg (by positivity) ht (neg_lt_zero.mpr hr)).symm
#align le_rpow_one_add_norm_iff_norm_le le_rpow_one_add_norm_iff_norm_le

variable (E)

theorem closedBall_rpow_sub_one_eq_empty_aux {r t : ℝ} (hr : 0 < r) (ht : 1 < t) :
    Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1) = ∅ := by
  rw [Metric.closedBall_eq_empty, sub_neg]
  exact Real.rpow_lt_one_of_one_lt_of_neg ht (by simp only [hr, Right.neg_neg_iff, inv_pos])
#align closed_ball_rpow_sub_one_eq_empty_aux closedBall_rpow_sub_one_eq_empty_aux

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {E}

theorem finite_integral_rpow_sub_one_pow_aux {r : ℝ} (n : ℕ) (hnr : (n : ℝ) < r) :
    (∫⁻ x : ℝ in Ioc 0 1, ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n)) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt n.cast_nonneg hnr
  have h_int :
    ∀ (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1),
      ENNReal.ofReal ((x ^ (-r⁻¹) - 1) ^ n) ≤ ENNReal.ofReal (x ^ (-(r⁻¹ * n))) := by
    intro x hx
    have hxr : 0 ≤ x ^ (-r⁻¹) := rpow_nonneg_of_nonneg hx.1.le _
    apply ENNReal.ofReal_le_ofReal
    rw [← neg_mul, rpow_mul hx.1.le, rpow_nat_cast]
    refine' pow_le_pow_of_le_left _ (by simp only [sub_le_self_iff, zero_le_one]) n
    rw [le_sub_iff_add_le', add_zero]
    refine' Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 _
    rw [Right.neg_nonpos_iff, inv_nonneg]
    exact hr.le
  refine' lt_of_le_of_lt (set_lintegral_mono (by measurability) (by measurability) h_int) _
  refine' integrable_on.set_lintegral_lt_top _
  rw [← intervalIntegrable_iff_integrable_Ioc_of_le zero_le_one]
  apply intervalIntegral.intervalIntegrable_rpow'
  rwa [neg_lt_neg_iff, inv_mul_lt_iff' hr, one_mul]
#align finite_integral_rpow_sub_one_pow_aux finite_integral_rpow_sub_one_pow_aux

theorem finite_integral_one_add_norm [MeasureSpace E] [BorelSpace E]
    [(@volume E _).IsAddHaarMeasure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    (∫⁻ x : E, ENNReal.ofReal ((1 + ‖x‖) ^ (-r))) < ∞ := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  -- We start by applying the layer cake formula
  have h_meas : Measurable fun ω : E => (1 + ‖ω‖) ^ (-r) := by measurability
  have h_pos : ∀ x : E, 0 ≤ (1 + ‖x‖) ^ (-r) := by intro x; positivity
  rw [lintegral_eq_lintegral_meas_le volume h_pos h_meas]
  -- We use the first transformation of the integrant to show that we only have to integrate from
  -- 0 to 1 and from 1 to ∞
  have h_int :
    ∀ (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)),
      (volume {a : E | t ≤ (1 + ‖a‖) ^ (-r)} : ENNReal) =
        volume (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1)) := by
    intro t ht
    congr 1
    ext x
    simp only [mem_set_of_eq, mem_closedBall_zero_iff]
    exact le_rpow_one_add_norm_iff_norm_le hr (mem_Ioi.mp ht) x
  rw [set_lintegral_congr_fun measurableSet_Ioi (ae_of_all volume <| h_int)]
  have hIoi_eq : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  have hdisjoint : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := by simp [disjoint_iff]
  rw [hIoi_eq, lintegral_union measurableSet_Ioi hdisjoint, ENNReal.add_lt_top]
  have h_int' :
    ∀ (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1),
      (volume (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1)) : ENNReal) =
        ENNReal.ofReal ((t ^ (-r⁻¹) - 1) ^ FiniteDimensional.finrank ℝ E) *
          volume (Metric.ball (0 : E) 1) := by
    intro t ht
    refine' volume.add_haar_closed_ball (0 : E) _
    rw [le_sub_iff_add_le', add_zero]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2 (by simp [hr.le])
  have h_meas' : Measurable fun a : ℝ => ENNReal.ofReal ((a ^ (-r⁻¹) - 1) ^ finrank ℝ E) := by
    measurability
  constructor
  -- The integral from 0 to 1:
  · rw [set_lintegral_congr_fun measurableSet_Ioc (ae_of_all volume <| h_int'),
      lintegral_mul_const _ h_meas', ENNReal.mul_lt_top_iff]
    left
    -- We calculate the integral
    exact ⟨finite_integral_rpow_sub_one_pow_aux (finrank ℝ E) hnr, measure_ball_lt_top⟩
  -- The integral from 1 to ∞ is zero:
  have h_int'' :
    ∀ (t : ℝ) (ht : t ∈ Ioi (1 : ℝ)),
      (volume (Metric.closedBall (0 : E) (t ^ (-r⁻¹) - 1)) : ENNReal) = 0 :=
    fun t ht => by rw [closedBall_rpow_sub_one_eq_empty_aux E hr ht, measure_empty]
  -- The integral over the constant zero function is finite:
  rw [set_lintegral_congr_fun measurableSet_Ioi (ae_of_all volume <| h_int''), lintegral_const 0,
    zero_mul]
  exact WithTop.zero_lt_top
#align finite_integral_one_add_norm finite_integral_one_add_norm

theorem integrable_one_add_norm [MeasureSpace E] [BorelSpace E] [(@volume E _).IsAddHaarMeasure]
    {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) : Integrable fun x : E => (1 + ‖x‖) ^ (-r) := by
  refine' ⟨by measurability, _⟩
  -- Lower Lebesgue integral
  have : (∫⁻ a : E, ‖(1 + ‖a‖) ^ (-r)‖₊) = ∫⁻ a : E, ENNReal.ofReal ((1 + ‖a‖) ^ (-r)) :=
    lintegral_nnnorm_eq_of_nonneg fun _ => rpow_nonneg_of_nonneg (by positivity) _
  rw [has_finite_integral, this]
  exact finite_integral_one_add_norm hnr
#align integrable_one_add_norm integrable_one_add_norm

theorem integrable_rpow_neg_one_add_norm_sq [MeasureSpace E] [BorelSpace E]
    [(@volume E _).IsAddHaarMeasure] {r : ℝ} (hnr : (finrank ℝ E : ℝ) < r) :
    Integrable fun x : E => ((1 : ℝ) + ‖x‖ ^ 2) ^ (-r / 2) := by
  have hr : 0 < r := lt_of_le_of_lt (finrank ℝ E).cast_nonneg hnr
  refine ((integrable_one_add_norm hnr).const_mul <| (2 : ℝ) ^ (r / 2)).mono'
    ?_ (eventually_of_forall fun x => ?_)
  · -- porting note: was `measurability`
    refine (((measurable_id.norm.pow_const _).const_add _).pow_const _).aestronglyMeasurable
  refine (abs_of_pos ?_).trans_le  (rpow_neg_one_add_norm_sq_le x hr)
  positivity
#align integrable_rpow_neg_one_add_norm_sq integrable_rpow_neg_one_add_norm_sq

