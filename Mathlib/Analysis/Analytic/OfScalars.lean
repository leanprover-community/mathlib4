/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
import Mathlib.Analysis.Analytic.Basic

/-!
# Scalar series

This file contains API for analytic functions `∑ cᵢ • xⁱ` defined in terms of scalars
`c₀, c₁, c₂, …`.
## Main definitions / results:
 * `FormalMultilinearSeries.ofScalars`: the formal power series `∑ cᵢ • xⁱ`.
 * `FormalMultilinearSeries.ofScalarsSum`: the sum of such a power series, if it exists, and zero
   otherwise.
 * `FormalMultilinearSeries.ofScalars_radius_eq_(zero/inv/top)_of_tendsto`:
   the ratio test for an analytic function defined in terms of a formal power series `∑ cᵢ • xⁱ`.
 * `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal`:
   the ratio test for an analytic function using ENNReal division for all values `ℝ≥0∞`.
-/

namespace FormalMultilinearSeries

section Field

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [TopologicalRing E] (c : ℕ → 𝕜)

/-- Formal power series of `∑ cᵢ • xⁱ` for some scalar field `𝕜` and ring algebra `E`-/
def ofScalars : FormalMultilinearSeries 𝕜 E E :=
  fun n ↦ c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

variable {E}

/-- The sum of the formal power series. Takes the value `0` outside the radius of convergence. -/
noncomputable def ofScalarsSum (x : E) := (ofScalars E c).sum x

theorem ofScalars_apply_eq (x : E) (n : ℕ) :
    ofScalars E c n (fun _ ↦ x) = c n • x ^ n := by
  simp [ofScalars]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
theorem ofScalars_apply_eq' (x : E) :
    (fun n ↦ ofScalars E c n (fun _ ↦ x)) = fun n ↦ c n • x ^ n := by
  simp [ofScalars]

theorem ofScalars_sum_eq (x : E) : ofScalarsSum c x =
    ∑' n, c n • x ^ n := tsum_congr fun n => ofScalars_apply_eq c x n

theorem ofScalarsSum_eq_tsum : ofScalarsSum c =
    fun (x : E) => ∑' n : ℕ, c n • x ^ n := funext (ofScalars_sum_eq c)

theorem ofScalars_apply_zero (n : ℕ) :
    (ofScalars E c n fun _ => 0) = Pi.single (f := fun _ => E) 0 (c 0 • 1) n := by
  rw [ofScalars]
  cases n <;> simp

@[simp]
theorem ofScalarsSum_zero : ofScalarsSum c (0 : E) = c 0 • 1 := by
  simp [ofScalarsSum_eq_tsum, ← ofScalars_apply_eq, ofScalars_apply_zero]

@[simp]
theorem ofScalars_of_subsingleton [Subsingleton E] {n : ℕ} : ofScalars E c n = 0 := by
  rw [ofScalars, smul_eq_zero (c := c n) (x := ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]
  exact Or.inr (ContinuousMultilinearMap.ext fun f ↦ Subsingleton.allEq _ _)

@[simp]
theorem ofScalarsSum_of_subsingleton [Subsingleton E] {x : E} : ofScalarsSum c x = 0 := by
  simp [Subsingleton.eq_zero x, Subsingleton.eq_zero (1 : E)]

@[simp]
theorem ofScalars_op [T2Space E] (x : E) :
    ofScalarsSum c (MulOpposite.op x) = MulOpposite.op (ofScalarsSum c x) := by
  simp [ofScalars, ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem ofScalars_unop [T2Space E] (x : Eᵐᵒᵖ) :
    ofScalarsSum c (MulOpposite.unop x) = MulOpposite.unop (ofScalarsSum c x) := by
  simp [ofScalars, ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

@[simp]
theorem ofScalars_eq_zero [Nontrivial E] (n : ℕ) : ofScalars E c n = 0 ↔ c n = 0 := by
  rw [ofScalars, smul_eq_zero (c := c n) (x := ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ ↦ 1
  simp

@[simp]
theorem ofScalars_eq_zero_of_scalar_zero (n : ℕ) (hc : c n = 0) : ofScalars E c n = 0 := by
  rw [ofScalars, hc, zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

end Field

section Normed

open Filter ENNReal
open scoped Topology NNReal

variable {𝕜 : Type*} (E : Type*) [NontriviallyNormedField 𝕜] [NormedRing E]
    [NormedAlgebra 𝕜 E] (c : ℕ → 𝕜) (n : ℕ)

theorem ofScalars_norm_eq_mul :
    ‖ofScalars E c n‖ = ‖c n‖ * ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E‖ := by
  rw [ofScalars, norm_smul (c n) (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

theorem ofScalars_norm_le (hn : n > 0) : ‖ofScalars E c n‖ ≤ ‖c n‖ := by
  simp only [ofScalars_norm_eq_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (ContinuousMultilinearMap.norm_mkPiAlgebraFin_le_of_pos hn))

@[simp]
theorem ofScalars_norm [NormOneClass E] : ‖ofScalars E c n‖ = ‖c n‖ := by
  simp [ofScalars_norm_eq_mul]

private theorem tendsto_succ_norm_div_norm {r r' : ℝ≥0} (hr' : r' ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      Tendsto (fun n ↦ ‖‖c (n + 1)‖ * r' ^ (n + 1)‖ /
        ‖‖c n‖ * r' ^ n‖) atTop (𝓝 ↑(r' * r)) := by
  simp_rw [norm_mul, norm_norm, mul_div_mul_comm, ← norm_div, pow_succ,
    mul_div_right_comm, div_self (pow_ne_zero _ (NNReal.coe_ne_zero.mpr hr')
    ), one_mul, norm_div, NNReal.norm_eq]
  exact mul_comm r' r ▸ hc.mul tendsto_const_nhds

theorem ofScalars_radius_le_inv_of_tendsto {r : ℝ≥0} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius ≥ ofNNReal r⁻¹ := by
  refine le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  rw [coe_lt_coe, NNReal.lt_inv_iff_mul_lt hr] at hr'
  by_cases hrz : r' = 0
  · simp [hrz]
  · apply FormalMultilinearSeries.le_radius_of_summable_norm
    refine Summable.of_norm_bounded_eventually (fun n ↦ ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · refine summable_of_ratio_test_tendsto_lt_one hr' ?_ ?_
      · refine (hc.eventually_ne (NNReal.coe_ne_zero.mpr hr)).mp (Eventually.of_forall ?_)
        aesop
      · simp_rw [norm_norm]
        exact tendsto_succ_norm_div_norm c hrz hc
    · filter_upwards [eventually_cofinite_ne 0] with n hn
      simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
      gcongr
      exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/-- The radius of convergence of a scalar series is the inverse of the non-zero limit
`fun n ↦ ‖c n.succ‖ / ‖c n‖`. -/
theorem ofScalars_radius_eq_inv_of_tendsto [NormOneClass E] {r : ℝ≥0} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r⁻¹ := by
  refine le_antisymm ?_ (ofScalars_radius_le_inv_of_tendsto E c hr hc)
  refine le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  rw [coe_le_coe, NNReal.le_inv_iff_mul_le hr]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
  contrapose! this
  apply not_summable_of_ratio_test_tendsto_gt_one this
  simp_rw [ofScalars_norm]
  exact tendsto_succ_norm_div_norm c (by aesop) hc

/-- A convenience lemma restating the result of `ofScalars_radius_eq_inv_of_tendsto` under
the inverse ratio. -/
theorem ofScalars_radius_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ofNNReal r := by
  suffices Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert hc.inv₀ (NNReal.coe_ne_zero.mpr hr) using 1
  simp

/-- The ratio test stating that if `‖c n.succ‖ / ‖c n‖` tends to zero, the radius is unbounded.
This requires that the coefficients are eventually non-zero as
`‖c n.succ‖ / 0 = 0` by convention. -/
theorem ofScalars_radius_eq_top_of_tendsto (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (hc' : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0)) : (ofScalars E c).radius = ⊤ := by
  refine radius_eq_top_of_summable_norm _ fun r' ↦ ?_
  by_cases hrz : r' = 0
  · apply Summable.comp_nat_add (k := 1)
    simp [hrz]
    exact (summable_const_iff 0).mpr rfl
  · refine Summable.of_norm_bounded_eventually (fun n ↦ ‖‖c n‖ * r' ^ n‖) ?_ ?_
    · apply summable_of_ratio_test_tendsto_lt_one zero_lt_one (hc.mp (Eventually.of_forall ?_))
      · simp only [norm_norm]
        exact mul_zero (_ : ℝ) ▸ tendsto_succ_norm_div_norm _ hrz (NNReal.coe_zero ▸ hc')
      · aesop
    · filter_upwards [eventually_cofinite_ne 0] with n hn
      simp only [norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
      gcongr
      exact ofScalars_norm_le E c n (Nat.pos_iff_ne_zero.mpr hn)

/-- If `‖c n.succ‖ / ‖c n‖` is unbounded, then the radius of convergence is zero. -/
theorem ofScalars_radius_eq_zero_of_tendsto [NormOneClass E]
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop atTop) : (ofScalars E c).radius = 0 := by
  suffices (ofScalars E c).radius ≤ 0 by aesop
  refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
  rw [← coe_zero, coe_le_coe]
  have := FormalMultilinearSeries.summable_norm_mul_pow _ hr
  contrapose! this
  apply not_summable_of_ratio_norm_eventually_ge one_lt_two
  · contrapose! hc
    apply not_tendsto_atTop_of_tendsto_nhds (a:=0)
    rw [not_frequently] at hc
    apply Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hc] with n hc'
    rw [ofScalars_norm, norm_mul, norm_norm, not_ne_iff, mul_eq_zero] at hc'
    cases hc' <;> aesop
  · filter_upwards [hc.eventually_ge_atTop (2*r⁻¹), eventually_ne_atTop 0] with n hc hn
    simp only [ofScalars_norm, norm_mul, norm_norm, norm_pow, NNReal.norm_eq]
    rw [mul_comm ‖c n‖, ← mul_assoc, ← div_le_div_iff, mul_div_assoc]
    · convert hc
      rw [pow_succ, div_mul_cancel_left₀, NNReal.coe_inv]
      aesop
    · aesop
    · refine Ne.lt_of_le (fun hr' ↦ Not.elim ?_ hc) (norm_nonneg _)
      rw [← hr']
      simp [this]

/-- This theorem combines the results of the .-/
theorem ofScalars_radius_eq_inv_of_tendsto_ENNReal [NormOneClass E] {r : ℝ≥0∞}
    (hc' : Tendsto (fun n ↦ ENNReal.ofReal ‖c n.succ‖ / ENNReal.ofReal ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = r⁻¹ := by
  rcases ENNReal.trichotomy r with (hr | hr | hr)
  · simp_rw [hr, inv_zero] at hc' ⊢
    by_cases h : (∀ᶠ (n : ℕ) in atTop, c n ≠ 0)
    · apply ofScalars_radius_eq_top_of_tendsto E c h ?_
      refine Tendsto.congr' ?_ <| (tendsto_toReal zero_ne_top).comp hc'
      filter_upwards [h]
      simp
    · apply (ofScalars E c).radius_eq_top_of_eventually_eq_zero
      simp only [eventually_atTop, not_exists, not_forall, Classical.not_imp, not_not] at h ⊢
      obtain ⟨ti, hti⟩ := eventually_atTop.mp (hc'.eventually_ne zero_ne_top)
      obtain ⟨zi, hzi, z⟩ := h ti
      refine ⟨zi, fun n hn ↦ ?_⟩
      induction n, hn using Nat.le_induction with
      | base => exact ofScalars_eq_zero_of_scalar_zero c zi z
      | succ n hmn a =>
        nontriviality E
        simp only [ofScalars_eq_zero] at a ⊢
        contrapose! hti
        exact ⟨n, hzi.trans hmn, ENNReal.div_eq_top.mpr (by simp [a, hti])⟩
  · simp_rw [hr, inv_top] at hc' ⊢
    apply ofScalars_radius_eq_zero_of_tendsto E c ((tendsto_add_atTop_iff_nat 1).mp ?_)
    refine tendsto_ofReal_nhds_top.mp (Tendsto.congr' ?_ ((tendsto_add_atTop_iff_nat 1).mpr hc'))
    filter_upwards [hc'.eventually_ne top_ne_zero] with n hn
    apply (ofReal_div_of_pos (Ne.lt_of_le (Ne.symm ?_) (norm_nonneg _))).symm
    aesop
  · have hr' := toReal_ne_zero.mp hr.ne.symm
    have hr'' := toNNReal_ne_zero.mpr hr' -- this result could go in ENNReal
    convert ofScalars_radius_eq_inv_of_tendsto E c hr'' ?_
    · simp [ENNReal.coe_inv hr'', ENNReal.coe_toNNReal (toReal_ne_zero.mp hr.ne.symm).2]
    · simp_rw [ENNReal.coe_toNNReal_eq_toReal]
      refine Tendsto.congr' ?_ <| (tendsto_toReal hr'.2).comp hc'
      filter_upwards [hc'.eventually_ne hr'.1, hc'.eventually_ne hr'.2]
      simp

end Normed

end FormalMultilinearSeries
