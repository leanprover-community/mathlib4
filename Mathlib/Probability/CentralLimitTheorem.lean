/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
The Central Limit Theorem
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

set_option backward.isDefEq.respectTransparency false
/-- `(1 + t/n + o(1/n)) ^ n → exp t` for `t ∈ ℂ`. -/
lemma tendsto_pow_exp_of_isLittleO {f : ℕ → ℂ} (t : ℂ)
    (hf : (fun n ↦ f n - (1 + t / n)) =o[atTop] fun n ↦ 1 / (n : ℝ)) :
    Tendsto (fun n ↦ f n ^ n) atTop (𝓝 (exp t)) := by
  let g n := f n - 1
  have fg n : f n = 1 + g n := by ring
  simp_rw [fg, add_sub_add_left_eq_sub] at hf ⊢
  apply tendsto_one_add_pow_exp_of_tendsto
  rw [← tendsto_sub_nhds_zero_iff]
  apply hf.tendsto_inv_smul_nhds_zero.congr'
  filter_upwards [eventually_ne_atTop 0] with n h0
  simpa [mul_sub] using mul_div_cancel₀ t (mod_cast h0)

lemma tendsto_sqrt_atTop : Tendsto (√·) atTop atTop := by
  simp_rw [Real.sqrt_eq_rpow]
  exact tendsto_rpow_atTop (by norm_num)

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

/-- The standard real Gaussian `𝓝 (0, 1)`. -/
abbrev stdGaussian : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- Sum of `n` random variables over `Fin n`, normalized by `1/√ n` for the
central limit theorem. -/
abbrev invSqrtMulSum {Ω} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (√n)⁻¹ * ∑ i : Fin n, X i ω

lemma map_invSqrtMulSum (μ : Measure Ω) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    μ.map (invSqrtMulSum X n)
      = ((μ.map (fun ω (i : Fin n) ↦ X i ω)).map (fun x ↦ ∑ i, x i)).map ((√n)⁻¹ * ·) := by
  rw [Measure.map_map, Measure.map_map]
  · rfl
  all_goals { fun_prop }

lemma measurable_invSqrtMulSum (n) (hX : ∀ n, Measurable (X n)) :
    Measurable (invSqrtMulSum X n) := by fun_prop

lemma aemeasurable_invSqrtMulSum {μ : Measure Ω} (n) (hX : ∀ n, Measurable (X n)) :
    AEMeasurable (invSqrtMulSum X n) μ := by fun_prop

set_option backward.isDefEq.respectTransparency false in
lemma charFun_sqrt_inv_mul_sum (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) {n : ℕ} {t : ℝ} :
    charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t =
      charFun (P.map (X 0)) ((√n)⁻¹ * t) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul', hindep.charFun_map_fun_finset_sum_eq_prod mX]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

lemma taylor_charFun_two {X : Ω → ℝ} (hX : Measurable X) {P : Measure Ω} [IsProbabilityMeasure P]
    (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) :
    (fun t ↦ charFun (P.map X) t - (1 - t ^ 2 / 2)) =o[𝓝 0] fun t ↦ t ^ 2 := by
  simp_rw [← taylorWithinEval_charFun_two_zero' (by fun_prop) h0 h1]
  convert taylor_isLittleO_univ ?_
  · simp
  · refine contDiff_charFun ?_
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 (.of_integral_ne_zero ?_)
    rw [integral_map]
    any_goals fun_prop
    simp_all

theorem central_limit {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P) (h0 : P[X 0] = 0)
    (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y P where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t ↦ ?_
    rw! [hY.map_eq, ProbabilityMeasure.coe_mk, charFun_gaussianReal]
    simp only [Real.sqrt_inv, ProbabilityMeasure.coe_mk, ofReal_zero, mul_zero, zero_mul,
      NNReal.coe_one, ofReal_one, one_mul, zero_sub]
    -- `⊢ Tendsto (fun n ↦ charFun (P.map (invSqrtMulSum X n)) t) atTop (𝓝 (cexp (-(t ^ 2 / 2))))`

    -- use existing results to rewrite the charFun
    simp_rw [charFun_sqrt_inv_mul_sum hindep hident]
    apply tendsto_pow_exp_of_isLittleO
    rw [← tendsto_sub_nhds_zero_iff]

    -- apply tendsto_pow_exp_of_isLittleO; suffices to show the base is (1 - t ^ 2 / 2n + o(1 / n))
    norm_cast
    rw [ofReal_exp]
    apply tendsto_pow_exp_of_isLittleO

    suffices (fun (n : ℕ) ↦
          charFun (Measure.map (X 0) P) ((√n)⁻¹ * t) - (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ)))
        =o[atTop] fun n ↦ ((√n)⁻¹ * t) ^ 2 by
      simp_rw [mul_comm _ t] at this ⊢
      simp_rw [mul_pow] at this
      convert this.of_const_mul_right (c := t ^ 2) using 3 with n
      · simp only [ofReal_neg, ofReal_div, ofReal_ofNat, ofReal_inv, inv_pow, ← ofReal_pow,
          Nat.cast_nonneg, Real.sq_sqrt, ofReal_natCast, add_right_inj]
        ring
      · simp

    have h_taylor : (fun t ↦ charFun (Measure.map (X 0) P) t - (1 - t ^ 2 / 2))
        =o[𝓝 0] fun t ↦ t ^ 2 := taylor_charFun_two (hX 0) h0 h1

    have h_tendsto : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
      have t_mul_inv_sqrt := Tendsto.const_mul t <| tendsto_inv_atTop_zero.comp <|
          tendsto_sqrt_atTop.comp <| tendsto_natCast_atTop_atTop
      rw [mul_zero] at t_mul_inv_sqrt
      convert t_mul_inv_sqrt using 2 with n
      simp only [Function.comp_apply]
      ring

    convert h_taylor.comp_tendsto h_tendsto using 2 with n n
    simp only [ofReal_inv, Function.comp_apply, ofReal_mul]
    ring_nf

end ProbabilityTheory
