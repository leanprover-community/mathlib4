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
 * `FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto`: the ratio test for an analytic function
   defined in terms of a formal power series `∑ cᵢ • xⁱ`.
-/

namespace FormalMultilinearSeries

section Field

open ContinuousMultilinearMap

variable {𝕜 : Type*} (E : Type*) [Field 𝕜] [Ring E] [Algebra 𝕜 E] [TopologicalSpace E]
  [TopologicalRing E] (c : ℕ → 𝕜)

/-- Formal power series of `∑ cᵢ • xⁱ` for some scalar field `𝕜` and ring algebra `E`-/
def ofScalars : FormalMultilinearSeries 𝕜 E E :=
  fun n ↦ c n • ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E

variable {E}

@[simp]
theorem ofScalars_eq_zero [Nontrivial E] (n : ℕ) : ofScalars E c n = 0 ↔ c n = 0 := by
  rw [ofScalars, smul_eq_zero (c := c n) (x := ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]
  refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
  use fun _ ↦ 1
  simp

@[simp]
theorem ofScalars_eq_zero_of_scalar_zero {n : ℕ} (hc : c n = 0) : ofScalars E c n = 0 := by
  rw [ofScalars, hc, zero_smul 𝕜 (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]

@[simp]
theorem ofScalars_series_eq_zero [Nontrivial E] : ofScalars E c = 0 ↔ c = 0 := by
  simp [FormalMultilinearSeries.ext_iff, funext_iff]

variable (𝕜) in
@[simp]
theorem ofScalars_series_eq_zero_of_scalar_zero : ofScalars E (0 : ℕ → 𝕜) = 0 := by
  simp [FormalMultilinearSeries.ext_iff]

@[simp]
theorem ofScalars_series_of_subsingleton [Subsingleton E] : ofScalars E c = 0 := by
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff]
  exact fun _ _ ↦ Subsingleton.allEq _ _

variable (𝕜) in
theorem ofScalars_series_injective [Nontrivial E] : Function.Injective (ofScalars E (𝕜 := 𝕜)) := by
  intro _ _
  refine Function.mtr fun h ↦ ?_
  simp_rw [FormalMultilinearSeries.ext_iff, ofScalars, ContinuousMultilinearMap.ext_iff,
    ContinuousMultilinearMap.smul_apply]
  push_neg
  obtain ⟨n, hn⟩ := Function.ne_iff.1 h
  refine ⟨n, fun _ ↦ 1, ?_⟩
  simp only [mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate, one_pow, ne_eq]
  exact (smul_left_injective 𝕜 one_ne_zero).ne hn

variable (c : ℕ → 𝕜)

@[simp]
theorem ofScalars_series_eq_iff [Nontrivial E] (c' : ℕ → 𝕜) :
    ofScalars E c = ofScalars E c' ↔ c = c' :=
  ⟨fun e => ofScalars_series_injective 𝕜 e, _root_.congrArg _⟩

theorem ofScalars_apply_zero (n : ℕ) :
    ofScalars E c n (fun _ => 0) = Pi.single (f := fun _ => E) 0 (c 0 • 1) n := by
  rw [ofScalars]
  cases n <;> simp

@[simp]
lemma coeff_ofScalars {𝕜 : Type*} [NontriviallyNormedField 𝕜] {p : ℕ → 𝕜} {n : ℕ} :
    (FormalMultilinearSeries.ofScalars 𝕜 p).coeff n = p n := by
  simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.ofScalars, List.prod_ofFn]

theorem ofScalars_add (c' : ℕ → 𝕜) : ofScalars E (c + c') = ofScalars E c + ofScalars E c' := by
  unfold ofScalars
  simp_rw [Pi.add_apply, Pi.add_def _ _]
  exact funext fun n ↦ Module.add_smul (c n) (c' n) (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)

theorem ofScalars_smul (x : 𝕜) : ofScalars E (x • c) = x • ofScalars E c := by
  unfold ofScalars
  simp [Pi.smul_def x _, smul_smul]

-- variable {E}

theorem ofScalars_apply_eq (x : E) (n : ℕ) :
    ofScalars E c n (fun _ ↦ x) = c n • x ^ n := by
  simp [ofScalars]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
theorem ofScalars_apply_eq' (x : E) :
    (fun n ↦ ofScalars E c n (fun _ ↦ x)) = fun n ↦ c n • x ^ n := by
  simp [ofScalars]

/-- The sum of the formal power series. Takes the value `0` outside the radius of convergence. -/
noncomputable def ofScalarsSum (x : E) := (ofScalars E c).sum x

-- theorem ofScalars_apply_eq (x : E) (n : ℕ) :
--     ofScalars E c n (fun _ ↦ x) = c n • x ^ n := by
--   simp [ofScalars]

-- /-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
-- theorem ofScalars_apply_eq' (x : E) :
--     (fun n ↦ ofScalars E c n (fun _ ↦ x)) = fun n ↦ c n • x ^ n := by
--   simp [ofScalars]

theorem ofScalars_sum_eq (x : E) : ofScalarsSum c x =
    ∑' n, c n • x ^ n := tsum_congr fun n => ofScalars_apply_eq c x n

theorem ofScalarsSum_eq_tsum : ofScalarsSum c =
    fun (x : E) => ∑' n : ℕ, c n • x ^ n := funext (ofScalars_sum_eq c)

@[simp]
theorem ofScalars_op [T2Space E] (x : E) :
    ofScalarsSum c (MulOpposite.op x) = MulOpposite.op (ofScalarsSum c x) := by
  simp [ofScalars, ofScalars_sum_eq, ← MulOpposite.op_pow, ← MulOpposite.op_smul, tsum_op]

@[simp]
theorem ofScalars_unop [T2Space E] (x : Eᵐᵒᵖ) :
    ofScalarsSum c (MulOpposite.unop x) = MulOpposite.unop (ofScalarsSum c x) := by
  simp [ofScalars, ofScalars_sum_eq, ← MulOpposite.unop_pow, ← MulOpposite.unop_smul, tsum_unop]

-- @[simp]
-- theorem ofScalars_eq_zero [Nontrivial E] (n : ℕ) : ofScalars E c n = 0 ↔ c n = 0 := by
--   rw [ofScalars, smul_eq_zero (c := c n) (x := ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n E)]
--   refine or_iff_left (ContinuousMultilinearMap.ext_iff.1.mt <| not_forall_of_exists_not ?_)
--   use fun _ ↦ 1
--   simp

end Field

section Normed

open Filter
open scoped Topology

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

/-- The radius of convergence of a scalar series is the inverse of the ratio of the norms of the
coefficients. -/
theorem ofScalars_radius_eq_inv_of_tendsto [NormOneClass E] {r : NNReal} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ENNReal.ofNNReal r⁻¹ := by
  have hc' {r' : NNReal} (hr' : (r' : ℝ) ≠ 0) :
    Tendsto (fun n ↦ ‖‖ofScalars E c (n + 1)‖ * r' ^ (n + 1)‖ /
      ‖‖ofScalars E c n‖ * r' ^ n‖) atTop (𝓝 ↑(r' * r)) := by
    simp_rw [norm_mul, norm_norm, ofScalars_norm, mul_div_mul_comm, ← norm_div, pow_succ,
      mul_div_right_comm, div_self (pow_ne_zero _ hr'), one_mul, norm_div, NNReal.norm_eq]
    exact mul_comm r' r ▸ Filter.Tendsto.mul hc tendsto_const_nhds
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  · rw [ENNReal.coe_le_coe, NNReal.le_inv_iff_mul_le hr]
    have := FormalMultilinearSeries.summable_norm_mul_pow _ hr'
    contrapose! this
    have hrz : (r' : ℝ) ≠ 0 := by aesop
    apply not_summable_of_ratio_test_tendsto_gt_one this
    exact hc' (by aesop)
  · rw [ENNReal.coe_lt_coe, NNReal.lt_inv_iff_mul_lt hr] at hr'
    by_cases hrz : r' = 0
    · simp [hrz]
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      refine summable_of_ratio_test_tendsto_lt_one hr' ?_ <| hc' (NNReal.coe_ne_zero.2 hrz)
      refine (Tendsto.eventually_ne hc (NNReal.coe_ne_zero.2 hr)).mp (Eventually.of_forall ?_)
      simp_rw [div_ne_zero_iff, ofScalars_norm, mul_ne_zero_iff]
      aesop

/-- A convenience lemma restating the result of `ofScalars_radius_eq_inv_of_tendsto` under
the inverse ratio. -/
theorem ofScalars_radius_eq_of_tendsto [NormOneClass E] {r : NNReal} (hr : r ≠ 0)
    (hc : Tendsto (fun n ↦ ‖c n‖ / ‖c n.succ‖) atTop (𝓝 r)) :
      (ofScalars E c).radius = ENNReal.ofNNReal r := by
  suffices Tendsto (fun n ↦ ‖c n.succ‖ / ‖c n‖) atTop (𝓝 r⁻¹) by
    convert ofScalars_radius_eq_inv_of_tendsto E c (inv_ne_zero hr) this
    simp
  convert (continuousAt_inv₀ <| NNReal.coe_ne_zero.mpr hr).tendsto.comp hc
  simp

end Normed

end FormalMultilinearSeries
