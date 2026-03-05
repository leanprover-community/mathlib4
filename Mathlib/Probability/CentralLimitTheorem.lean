/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
The Central Limit Theorem
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}

set_option backward.isDefEq.respectTransparency false in
lemma charFun_sqrt_inv_mul_sum (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) {n : ℕ} {t : ℝ} :
    charFun (P.map (fun ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t =
      charFun (P.map (X 0)) ((√n)⁻¹ * t) ^ n := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul', hindep.charFun_map_fun_finset_sum_eq_prod mX]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

lemma tendsto_charFun_sqrt_inv_mul_pow {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h0 : P[X] = 0) (h1 : P[X ^ 2] = 1) (t : ℝ) :
    Tendsto (fun (n : ℕ) ↦ charFun (P.map X) ((√n)⁻¹ * t) ^ n) atTop (𝓝 (exp (- t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  suffices (fun (n : ℕ) ↦ charFun (Measure.map X P) ((√n)⁻¹ * t) -
      (1 + (-(((√n)⁻¹ * t) ^ 2 / 2) : ℂ))) =o[atTop] fun n ↦ ((√n)⁻¹ * t) ^ 2 by
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert this using 4 with n <;> norm_cast <;> simp [field]
  have : Tendsto (fun (n : ℕ) ↦ (√n)⁻¹ * t) atTop (𝓝 0) := by
    rw [← zero_mul t]
    exact .mul_const t (tendsto_inv_atTop_zero.comp <| Real.tendsto_sqrt_atTop.comp <|
      tendsto_natCast_atTop_atTop)
  convert (taylor_charFun_two hX h0 h1).comp_tendsto this using 2
  simp
  ring

theorem tendstoInDistribution_sqrt_inv_mul_sum {Y : Ω → ℝ} (hY : HasLaw Y (gaussianReal 0 1) P)
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω) atTop Y P where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t ↦ ?_
    rw! [hY.map_eq]
    simpa [charFun_sqrt_inv_mul_sum hindep hident, charFun_gaussianReal, neg_div] using
      tendsto_charFun_sqrt_inv_mul_pow (hident 0).aemeasurable_fst h0 h1 t

lemma memLp_two_of_variance_ne_zero {Y : Ω → ℝ} (mY : AEMeasurable Y P) (h : Var[Y; P] ≠ 0) :
    MemLp Y 2 P := by
  contrapose! h
  rw [← evariance_eq_top_iff mY.aestronglyMeasurable] at h
  rw [variance, h, ENNReal.toReal_top]

private theorem tendstoInDistribution_sqrt_mul_var_inv_mul_sum_sub {Y : Ω → ℝ}
    (hY : HasLaw Y (gaussianReal 0 1) P)
    (hX : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y P := by
  have mX0 := (hident 0).aemeasurable_fst
  have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1 <|
    (memLp_two_of_variance_ne_zero mX0 hX).mono_exponent (by simp)
  have this (n : ℕ) ω : (√(n * Var[X 0; P]))⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]) =
      (√n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - P[X 0]) / √Var[X 0; P] := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp [field]
  simp_rw [this]
  convert tendstoInDistribution_sqrt_inv_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow]
    rw [integral_div, ← variance_eq_integral mX0, Real.sq_sqrt (variance_nonneg _ _), div_self hX]
  · exact hindep.comp (fun _ x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)
  · convert fun n ↦ (hident n).comp (u := fun x ↦ (x - P[X 0]) / √Var[X 0; P]) (by fun_prop)

theorem tendstoInDistribution_sqrt_inv_mul_sum_sub {Y : Ω → ℝ}
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P)
    (hX : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * P[X 0]))
      atTop Y P := by
  have : HasLaw (fun ω ↦ Y ω / √Var[X 0; P]) (gaussianReal 0 1) P := by
    convert gaussianReal_div_const hY _
    · simp
    · ext; simp [hX]
  have := tendstoInDistribution_sqrt_mul_var_inv_mul_sum_sub this hX hindep hident
  convert this.continuous_comp (g := (√Var[X 0; P] * ·)) (by fun_prop)
  · simp [field]
    field_simp [hX]
  · ext
    simp [field]
    field_simp [hX]

end ProbabilityTheory
