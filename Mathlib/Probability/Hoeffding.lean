/-
Copyright (c) 2024 Kei Tsukamoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kazumi Kasaura, Naoto Onda, Sho sonoda, Yuma Mizuno
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Notation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Variance

/-!
# Hoeffding's lemma

This file states Hoeffding's lemma. We introduce cumulant to complete the proof.

## Main results

* `ProbabilityTheory.tilt_first_deriv`: derivation of `μ[exp (t * X ω)]` is
  `μ[exp (t * X ω) * X ω]`. In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof.
* `ProbabilityTheory.tilt_second_deriv`: derivation of `μ[fun ω ↦ rexp (t * X ω) * X ω]` is
  `μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]`. In order to deal with the differentiation of
  parametric integrals, `hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof.
* `ProbabilityTheory.cum_deriv_one`: first derivative of cumulant `log μ[rexp (t * X ω))]`.
  It can be described by exponential tilting.
* `ProbabilityTheory.cum_deriv_two`: second derivative of cumulant `log μ[rexp (t * X ω))]`.
* `ProbabilityTheory.hoeffding`: Hoeffding's Lemma states that for a random variable `X` with
  `E[X] = 0` (zero mean) and `a ≤ X ≤ b` almost surely, the inequality
  `μ[exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.

## References

* Martin J. Wainwright. High-Dimensional Statistics. Cambridge university press, 2019. Chapter 2
* Mehryar Mohri. Foundations of Machine Learning. The MIT Press, 2018. Chapter D

## Tags

hoeffding's lemma, cumulant
-/

open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω := by volume_tac)

lemma measurable_expt (X : Ω → ℝ) (t : ℝ) (hX : AEMeasurable X μ) :
    AEStronglyMeasurable (fun ω ↦ rexp (t * (X ω))) μ :=
  aestronglyMeasurable_iff_aemeasurable.mpr <| measurable_exp.comp_aemeasurable' (hX.const_mul t)

lemma integrable_expt [IsFiniteMeasure μ] (X : Ω → ℝ) (t b : ℝ) (ht : t > 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, X ω ≤ b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have hm1 : HasFiniteIntegral (fun ω ↦ rexp (t * X ω)) μ := by
    have b' : ∀ᵐ ω ∂μ, rexp (t * X ω) ≤ rexp (t * b) := by
      filter_upwards [hb] with ω hb
      using exp_le_exp.mpr (mul_le_mul_of_nonneg_left hb (le_of_lt ht))
    have p : ∀ᵐ ω ∂μ, ‖rexp (t * X ω)‖₊ ≤ rexp (t * b) := by
      filter_upwards [b'] with ω b'
      rw [(by simp only [coe_nnnorm, norm_eq_abs, abs_exp] : ‖rexp (t * X ω)‖₊ = rexp (t * X ω))]
      exact b'
    have p'' : ∫⁻ ω, ‖rexp (t * X ω)‖₊ ∂μ ≤ ∫⁻ _, ‖rexp (t * b)‖₊ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [p] with ω p
      simp only [ENNReal.coe_le_coe]
      rw [← (by simp only [coe_nnnorm, norm_eq_abs, abs_exp] : ‖rexp (t * b)‖₊ = rexp (t * b))] at p
      exact p
    suffices ∫⁻ _, ↑‖rexp (t * b)‖₊ ∂μ < ⊤ from lt_of_le_of_lt p'' this
    simp only [lintegral_const]
    apply ENNReal.mul_lt_top ENNReal.coe_lt_top (IsFiniteMeasure.measure_univ_lt_top)
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr <|
    measurable_exp.comp_aemeasurable' (hX.const_mul t), hm1⟩

lemma integrable_expt_bound[IsFiniteMeasure μ] {X : Ω → ℝ} {t a b : ℝ} (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable (fun ω ↦ exp (t * (X ω))) μ := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  cases lt_trichotomy t 0 with
  | inr ht => cases ht with
    | inr ht => exact integrable_expt μ X t b ht hX (h.mono fun ω h ↦ h.2)
    | inl ht => rw [ht]; simp only [zero_mul, exp_zero, integrable_const]
  | inl ht =>
    rw [(by ext ω; rw [(by ring : - t * (- X ω) = t * X ω)] :
      (fun ω ↦ rexp (t * X ω)) = (fun ω ↦ rexp (- t * (- X ω))))]
    exact integrable_expt _ _ _ _ (by linarith : -t > 0) (AEMeasurable.neg hX)
      (by filter_upwards [ha] with ω ha using neg_le_neg ha)

lemma expt_pos [IsFiniteMeasure μ] [NeZero μ] (X : Ω → ℝ) (t a b : ℝ)
    (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    0 < μ[fun ω ↦ exp (t * (X ω))] :=
  integral_exp_pos <| integrable_expt_bound μ hX h

lemma tilt_var_bound [IsProbabilityMeasure μ] (a b t : ℝ) (X : Ω → ℝ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hX : AEMeasurable X μ) :
    variance X (μ.tilted (fun ω ↦ t * X ω)) ≤ ((b - a) / 2) ^ 2 := by
  have : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
    isProbabilityMeasure_tilted (integrable_expt_bound μ hX h)
  exact variance_le_sq_of_bounded
      ((tilted_absolutelyContinuous μ fun ω ↦ t * X ω) h)
      (AEMeasurable.mono_ac hX (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))

theorem integrable_bounded [IsFiniteMeasure μ] (a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    Integrable X μ := by
  have m1 : HasFiniteIntegral X μ := by
    apply (hasFiniteIntegral_const (max ‖a‖ ‖b‖)).mono'
    filter_upwards [h.mono fun ω h ↦ h.1, h.mono fun ω h ↦ h.2] with ω using abs_le_max_abs_abs
  exact ⟨aestronglyMeasurable_iff_aemeasurable.mpr hX, m1⟩

/-- Derivation of `μ[exp (t * X ω)]` is `μ[exp (t * X ω) * X ω]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_first_deriv [IsFiniteMeasure μ] [NeZero μ] (t a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b):
    let g := fun t ↦ μ[fun ω ↦ rexp (t * X ω)]
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ → HasDerivAt g (g' t) t := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω))
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
    simp only [this.2, implies_true]
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · exact Filter.Eventually.of_forall
      (by intro t'; apply measurable_expt _ _ _ hX : ∀ (x : ℝ), AEStronglyMeasurable (e x) μ)
  · simp only [e]; apply integrable_expt_bound _ hX h
  · simp only [e']
    apply AEMeasurable.aestronglyMeasurable;
    apply AEMeasurable.mul _ hX
    apply Measurable.comp_aemeasurable' _ _
    · exact measurable_exp
    · exact AEMeasurable.const_mul hX t
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * |X ω|
    have p : ∀ y, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x y‖ ≤ bound y := by
      intros y x b1
      calc
      _ = |rexp (x * X y)| * |X y| := abs_mul (rexp (x * X y)) (X y)
      _ = rexp (x * X y) * |X y| := by simp only [abs_exp]
      _ ≤ rexp (|x * X y|) * |X y| :=
        mul_le_mul_of_nonneg_right (exp_le_exp.mpr (le_abs_self (x * X y))) (abs_nonneg (X y))
      _ = rexp (|x| * |X y|) * |X y| := by
        rw [abs_mul x (X y)]
      _ ≤ rexp ((2 * |t| + 1) * |X y|) * |X y| := by
        have p2 : |x| ≤ 2 * |t| + 1 := by
          simp only [Metric.mem_ball] at b1
          linarith [le_trans' (le_of_lt b1) (abs_sub_abs_le_abs_sub x t)]
        exact mul_le_mul_of_nonneg_right
          (exp_le_exp.mpr (mul_le_mul_of_nonneg_right p2 (abs_nonneg (X y)))) (abs_nonneg (X y))
    exact ae_of_all μ p
  · apply MeasureTheory.Integrable.bdd_mul'
    · exact MeasureTheory.Integrable.abs (integrable_bounded μ a b X hX h)
    · apply measurable_expt μ (fun ω ↦ |X ω|) (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [ha, hb] with ω ha hb
      have p0' : ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ rexp ((2 * |t| + 1) * |c|) := by
        simp only [norm_eq_abs, abs_exp, exp_le_exp]
        exact mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
          (abs_le_max_abs_abs ha hb)) (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
      exact p0'
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

/-- Derivation of `μ[fun ω ↦ rexp (t * X ω) * X ω]` is `μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]`.
In order to deal with the differentiation of parametric integrals,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are used in the proof. -/
theorem tilt_second_deriv  [IsFiniteMeasure μ] (t a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
    let g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]
    Integrable (fun ω ↦ rexp (t * X ω) * (X ω ^ 2)) μ → HasDerivAt g (g' t) t := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  set c := max ‖a‖ ‖b‖
  set e := (fun t ↦ fun ω ↦ rexp (t * X ω) * X ω)
  set e' := (fun t ↦ fun ω ↦ rexp (t * X ω) * (X ω ^ 2))
  suffices MeasureTheory.Integrable (e' t) μ ∧
    HasDerivAt (fun t ↦ μ[e t]) (μ[e' t]) t from by
    simp only [this.2, implies_true]
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
  · exact LE.le.trans_lt (abs_nonneg t) (lt_add_one |t|)
  · have u : ∀ (x : ℝ), AEStronglyMeasurable (e x) μ := by
      intro t'
      dsimp only [e]
      rw [aestronglyMeasurable_iff_aemeasurable]
      apply AEMeasurable.mul _ hX
      exact Measurable.comp_aemeasurable' measurable_exp (AEMeasurable.const_mul hX t')
    exact Filter.Eventually.of_forall u
  · simp only [e];
    apply MeasureTheory.Integrable.bdd_mul'
      (integrable_bounded μ a b X hX h) (measurable_expt μ X t hX)
    · filter_upwards [ha, hb] with ω ha hb
      have q00 : ‖rexp (t * X ω)‖ ≤ rexp (|t| * c) := by
        simp only [norm_eq_abs, abs_exp, exp_le_exp]
        calc
        _ ≤ |t * X ω| := le_abs_self (t * X ω)
        _ = |t| * |X ω| := abs_mul t (X ω)
        _ ≤ |t| * c := by
          apply mul_le_mul_of_nonneg_left
          rw [← (by dsimp only [c]; simp only
            [norm_eq_abs, abs_eq_self, le_max_iff, abs_nonneg, or_self] :
            |c| = c)]
          exact le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb)
          exact abs_nonneg t
      exact q00
  · dsimp only [e']
    rw [aestronglyMeasurable_iff_aemeasurable]
    apply AEMeasurable.mul
    · apply Measurable.comp_aemeasurable' _ _
      · exact measurable_exp
      · exact AEMeasurable.const_mul hX t
    exact AEMeasurable.pow_const hX 2
  · set bound := fun ω ↦ rexp ((2 * |t| + 1) * |X ω|) * (|X ω| ^ 2)
    suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1), ‖e' x ω‖ ≤ bound ω from ae_of_all μ this
    intros ω x h
    dsimp [e', bound]
    simp only [sq_abs]
    have h' : |rexp (x * X ω) * X ω ^ 2| ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2 := by
      calc
      _ = |rexp (x * X ω)| * |(X ω ^ 2)| := abs_mul (rexp (x * X ω)) (X ω ^ 2)
      _ = rexp (x * X ω) * (X ω ^ 2) := by simp only [abs_exp, abs_pow, sq_abs]
      _ ≤ rexp ((2 * |t| + 1) * |X ω|) * X ω ^ 2 := by
        suffices rexp (x * X ω) ≤
          rexp ((2 * |t| + 1) * |X ω|) from mul_le_mul_of_nonneg_right this (sq_nonneg (X ω))
        simp only [exp_le_exp]
        calc
        _ ≤ |x * X ω| := le_abs_self (x * X ω)
        _ = |x| * |X ω| := abs_mul x (X ω)
        _ ≤ (2 * |t| + 1) * |X ω| := by
          suffices |x| ≤ 2 * |t| + 1 from mul_le_mul_of_nonneg_right this (abs_nonneg (X ω))
          simp only [Metric.mem_ball] at h
          linarith [le_trans' (le_of_lt h) (abs_sub_abs_le_abs_sub x t)]
    exact h'
  · apply MeasureTheory.Integrable.bdd_mul'
    · simp only [sq_abs]
      rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul'
        (integrable_bounded μ a b X hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      · filter_upwards [ha, hb] with x ha hb
        exact (by simp only [norm_eq_abs]; exact
          le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb) : ‖X x‖ ≤ |c|)
    · apply measurable_expt μ (fun ω ↦ |X ω|) (2 * |t| + 1) _
      apply Measurable.comp_aemeasurable' _ hX
      apply measurable_norm
    · filter_upwards [ha, hb] with ω ha hb
      have p0 : ‖rexp ((2 * |t| + 1) * |X ω|)‖ ≤ ‖rexp ((2 * |t| + 1) * c)‖ := by
        simp only [norm_eq_abs, abs_exp, exp_le_exp]
        rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
        exact mul_le_mul_of_nonneg_left
          (le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb))
          (by linarith [abs_nonneg t] : 0 ≤ 2 * |t| + 1)
      exact p0
  suffices ∀ ω, ∀ x ∈ Metric.ball t (|t| + 1),
    HasDerivAt (fun x ↦ e x ω) (e' x ω) x from ae_of_all μ this
  intros ω x _
  dsimp only [e, e']
  suffices HasDerivAt (fun x ↦ rexp (x * X ω)) (rexp (x * X ω) * X ω) x from by
    rw [(by ring : rexp (x * X ω) * X ω ^ 2 = (rexp (x * X ω) * X ω) * X ω)]
    exact HasDerivAt.mul_const this (X ω)
  exact HasDerivAt.exp (hasDerivAt_mul_const (X ω))

theorem integrable_deriv_expt [IsFiniteMeasure μ] (t a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b):
    Integrable (fun ω ↦ rexp (t * X ω) * X ω) μ := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  apply MeasureTheory.Integrable.bdd_mul'
    (integrable_bounded μ a b X hX h) (measurable_expt _ _ _ hX)
  · set c := max ‖a‖ ‖b‖
    filter_upwards [ha, hb] with ω ha hb
    have q0 : ‖rexp (t * X ω)‖ ≤ ‖rexp (|t| * c)‖ := by
      simp only [norm_eq_abs, abs_exp, exp_le_exp]
      rw [← (abs_eq_self.mpr (le_trans' (le_max_left |a| ‖b‖) (abs_nonneg a)) : |c| = c)]
      calc
      _ ≤ |t * X ω| := le_abs_self (t * X ω)
      _ = |t| * |X ω| := abs_mul t (X ω)
      _ ≤ |t| * |c| :=
        mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
          (abs_le_max_abs_abs ha hb) : |X ω| ≤ |c|) (abs_nonneg t)
    exact q0

theorem integral_tilted [IsFiniteMeasure μ] [NeZero μ]
    (t : ℝ) (f : ℝ → ℝ) (X : Ω → ℝ) (hX : AEMeasurable X μ):
    (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ f (X ω)] =
    (μ[fun ω ↦ rexp (t * X ω) * f (X ω)]) / μ[fun ω ↦ rexp (t * X ω)] := by
  calc
  _ = (∫ ω, ((∂Measure.tilted μ fun ω ↦ t * X ω/∂μ) ω).toReal • f (X ω) ∂μ) :=
    Eq.symm (MeasureTheory.integral_rnDeriv_smul (tilted_absolutelyContinuous μ fun ω ↦ t * X ω))
  _ = ∫ ω, (rexp (t * X ω) / μ[fun ω ↦ rexp (t * X ω)]) * f (X ω) ∂μ := by
    apply integral_congr_ae
    have w : (μ.tilted fun ω ↦ t * X ω).rnDeriv μ =ᵐ[μ]
      fun ω ↦ ENNReal.ofReal (Real.exp (t * X ω) / ∫ ω, Real.exp (t * X ω) ∂μ) := by
        apply MeasureTheory.rnDeriv_tilted_left_self
        apply AEMeasurable.const_mul _ t
        exact hX
    filter_upwards [w] with ω w
    rw [w]
    simp only [smul_eq_mul, mul_eq_mul_right_iff, ENNReal.toReal_ofReal_eq_iff]
    left
    have q2 : 0 ≤ μ[fun ω ↦ rexp (t * X ω)] := by
      apply integral_nonneg
      apply Pi.le_def.mpr _
      intro i
      simp only [Pi.zero_apply]
      exact exp_nonneg (t * X i)
    exact div_nonneg (exp_nonneg (t * X ω)) q2
  _ = (∫ ω, (rexp (t * X ω) * f (X ω)) / (μ[fun ω ↦ rexp (t * X ω)]) ∂μ) := by
    apply integral_congr_ae
    apply ae_of_all μ
    intro a
    simp only
    ring
  _ = (∫ ω, rexp (t * X ω) * f (X ω) ∂μ) / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_div (μ[fun ω ↦ rexp (t * X ω)]) fun a ↦ rexp (t * X a) * f (X a)

/-! ### Derivatives of cumulant-/

/-- First derivative of cumulant `log (∫ ω, (rexp (t * X ω)) a ∂μ)`.
It can be described by exponential tilting.-/
theorem cum_deriv_one [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let f := fun t ↦ log (μ[fun ω ↦ rexp (t * X ω)])
    let f' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω)) [X]
    ∀ x : ℝ, HasDerivAt f (f' x) x := by
  intros f f' t
  set g := fun t ↦ μ[fun ω ↦ rexp (t * X ω)]
  set g' := fun t ↦ μ[fun ω ↦ rexp (t * X ω) * X ω]
  dsimp [f']
  have r0 : ((μ.tilted (fun ω ↦ t * X ω)) [fun ω ↦ id (X ω)]) =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted μ t id X hX
  simp at r0
  rw [r0]
  apply HasDerivAt.log
  · exact tilt_first_deriv μ _ _ _ _ hX h (integrable_deriv_expt μ t a b X hX h)
  · exact (by linarith [expt_pos μ X t a b hX h] : ∫ ω, rexp (t * X ω) ∂μ ≠ 0)

/-- Second derivative of cumulant `log μ[rexp (t * X ω))]`-/
theorem cum_deriv_two [IsFiniteMeasure μ] [NeZero μ] (a b : ℝ)
    (X : Ω → ℝ) (hX : AEMeasurable X μ) (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    let g' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X];
    let g'' := fun t ↦ (μ.tilted (fun ω ↦ t * X ω)) [X ^ 2] - (μ.tilted (fun ω ↦ t * X ω))[X] ^ 2;
    ∀ x : ℝ, HasDerivAt g' (g'' x) x := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h ↦ h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h ↦ h.2
  intro g' g'' t
  have r0 : (fun t ↦ ((μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)])) =
    fun t ↦ μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] := by
    ext t
    exact integral_tilted μ t id X hX
  have r01 : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ id (X ω)]  =
    μ[fun ω ↦ rexp (t * X ω) * id (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted μ t id X hX
  have r0' : (μ.tilted (fun ω ↦ t * X ω))[fun ω ↦ (fun s ↦ s ^ 2) (X ω)] =
    μ[fun ω ↦ rexp (t * X ω) * (fun s ↦ s ^ 2) (X ω)] / μ[fun ω ↦ rexp (t * X ω)] :=
    integral_tilted μ t (fun x ↦ x ^ 2) X hX
  simp only [id_eq] at r0 r0' r01
  dsimp [g', g'']
  rw [r0, r0', r01]
  field_simp
  have p : ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) / μ[fun ω ↦ rexp (t * X ω)]) =
  ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * (μ[fun ω ↦ rexp (t * X ω)])) /
  ((μ[fun ω ↦ rexp (t * X ω)]) * (μ[fun ω ↦ rexp (t * X ω)])) := by
    apply Eq.symm (mul_div_mul_right (∫ ω, rexp (t * X ω) * X ω ^ 2 ∂μ)
    (μ[fun ω ↦ rexp (t * X ω)]) _)
    exact (by linarith [expt_pos μ X t a b hX h] : ∫ ω, rexp (t * X ω) ∂μ ≠ 0)
  rw [p, Eq.symm (pow_two (∫ ω, rexp (t * X ω) ∂μ))]
  have p'' : (((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) *
    (μ[fun ω ↦ rexp (t * X ω)])) / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2 -
  (μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2 / (μ[fun ω ↦ rexp (t * X ω)]) ^ 2) =
  ((μ[fun ω ↦ exp (t * (X ω)) * (X ω) ^ 2] *
    μ[fun ω ↦ exp (t * (X ω))]) -
    (μ[fun ω ↦ exp (t * (X ω)) * X ω] * μ[fun ω ↦ exp (t * (X ω)) * X ω])) /
    (μ[fun ω ↦ exp (t * (X ω))] ^ 2) := by
    rw [Eq.symm (pow_two (∫ ω, (fun ω ↦ rexp (t * X ω) * X ω) ω ∂μ))]
    exact
      div_sub_div_same ((μ[fun ω ↦ rexp (t * X ω) * X ω ^ 2]) * μ[fun ω ↦ rexp (t * X ω)])
        ((μ[fun ω ↦ rexp (t * X ω) * X ω]) ^ 2) ((μ[fun ω ↦ rexp (t * X ω)]) ^ 2)
  rw [p'']
  apply HasDerivAt.div
  · set c := max ‖a‖ ‖b‖
    suffices ∀ᵐ ω ∂μ, HasDerivAt (fun x ↦ rexp (x * X ω)) (rexp (t * X ω) * X ω) t from by
      apply tilt_second_deriv  μ _ _ _ _ hX h
      apply MeasureTheory.Integrable.bdd_mul'
      rw [(by ext ω; ring : (fun ω ↦ X ω ^ 2) = (fun ω ↦ X ω * X ω))]
      apply MeasureTheory.Integrable.bdd_mul'
        (integrable_bounded μ a b X hX h) (aestronglyMeasurable_iff_aemeasurable.mpr hX)
      filter_upwards [ha, hb] with x ha hb
      exact (by simp only [norm_eq_abs];
                exact le_trans' (le_abs_self (max ‖a‖ ‖b‖)) (abs_le_max_abs_abs ha hb) :
                ‖X x‖ ≤ |c|)
      exact measurable_expt μ X t hX
      simp only [norm_eq_abs, abs_exp]
      filter_upwards [ha, hb] with ω ha hb
      have r0 : rexp (t * X ω) ≤ rexp (|t| * |c|) := by
        simp only [exp_le_exp]
        calc
        _ ≤ |t * X ω| := le_abs_self (t * X ω)
        _ = |t| * |X ω| := abs_mul t (X ω)
        _ ≤ |t| * |c| := mul_le_mul_of_nonneg_left (le_trans' (le_abs_self (max ‖a‖ ‖b‖))
                        (abs_le_max_abs_abs ha hb)) (abs_nonneg t)
      exact r0
    filter_upwards
    intro ω
    apply HasDerivAt.exp (hasDerivAt_mul_const (X ω))
  · apply (tilt_first_deriv _ _ _ _ _ hX h)
          (integrable_deriv_expt μ t a b X hX h)
  · exact (by linarith [expt_pos μ X t a b hX h] : ∫ ω, rexp (t * X ω) ∂μ ≠ 0)

/-! ### Hoeffding's lemma restricted to t ≥ 0-/

theorem hoeffding_nonneg [IsProbabilityMeasure μ]
    (t a b : ℝ) (X : Ω → ℝ) (ht : 0 ≤ t) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    μ[fun ω ↦ exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8) := by
  by_cases w : t = 0;
    · rw [w]; simp only [zero_mul, exp_zero, integral_const, measure_univ,
    ENNReal.one_toReal, smul_eq_mul, mul_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, le_refl]
  suffices log (μ[fun ω ↦ exp (t * (X ω))]) ≤ t^2 * (b - a)^2 / 8 from
    (log_le_iff_le_exp (expt_pos μ X t a b hX h)).mp this
  set f : ℝ → ℝ := fun t ↦ log (μ[fun ω ↦ exp (t * (X ω))])
  have hf : f 0 = 0 := by simp only
    [zero_mul, exp_zero, integral_const, measure_univ, ENNReal.one_toReal,
    smul_eq_mul, mul_one, log_one, f]
  set f' : ℝ → ℝ := fun t ↦ (μ.tilted (fun ω ↦ t * X ω))[X]
  have hf' : f' 0 = 0 := by
    dsimp only [f']
    simp only [zero_mul, tilted_const', measure_univ, inv_one, one_smul]
    exact h0
  set f'' : ℝ → ℝ := fun t ↦ variance X (μ.tilted (fun ω ↦ t * X ω))
  have q : ∀ x : ℝ, ∃ c ∈ (Set.Ioo 0 t), f t = f 0 + f' 0 * t + f'' c * t ^ 2 / 2 := by
    let A := (f t - f 0 - f' 0 * t) * 2 / t ^ 2
    have q0 : f t = f 0 + f' 0 * t + A * t ^ 2 / 2 := by
      have q0' : A * t ^ 2 = (f t - f 0 - f' 0 * t) * 2 := by
        calc
        _ = (f t - f 0 - f' 0 * t) * 2 * t ^ 2 / t ^ 2 :=
          Eq.symm (mul_div_right_comm ((f t - f 0 - f' 0 * t) * 2) (t ^ 2) (t ^ 2))
        _ = (f t - f 0 - f' 0 * t) * 2 * (t ^ 2 / t ^ 2) := by ring
        _ = (f t - f 0 - f' 0 * t) * 2 := by field_simp only
      rw [q0']
      ring
    set g : ℝ → ℝ := fun x ↦ f t - f x - f' x * (t - x) - A * (t - x) ^ 2 / 2
    have q1 : g 0 = 0 := by
      dsimp only [g, A]
      calc
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * t ^ 2 / t ^ 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 * (t ^ 2 / t ^ 2) := by ring
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) * 2 / 2 := by field_simp
      _ = f t - f 0 - f' 0 * t - (f t - f 0 - f' 0 * t) := by ring
      _ = 0 := by ring
    have q2 : g t = 0 := by
      dsimp only [g]
      simp only [sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, zero_div]
    set g' : ℝ → ℝ := fun x ↦ - f'' x * (t - x) + A * (t - x)
    have q3 : ∀ x : ℝ, HasDerivAt g (g' x) x := by
      intro x
      apply HasDerivAt.add
      · rw [← (by ring : 0 - f' x + (f' x - f'' x * (t - x)) = - f'' x * (t - x))]
        apply ((hasDerivAt_const x _).sub (cum_deriv_one μ a b X hX h x)).add
        convert (cum_deriv_two μ a b X hX h x).mul ((hasDerivAt_id' x).add_const (-t)) using 1
        · ext; ring
        · dsimp [f', f'']
          have p : variance X (Measure.tilted μ fun ω ↦ x * X ω) =
              (μ.tilted fun ω ↦ x * X ω)[X ^ 2] - ((μ.tilted fun ω ↦ x * X ω)[X]) ^ 2 := by
            have : IsProbabilityMeasure (μ.tilted fun ω ↦ x * X ω) :=
              isProbabilityMeasure_tilted (integrable_expt_bound μ hX h)
            have hμ := tilted_absolutelyContinuous μ fun ω ↦ x * X ω
            apply variance_def' <|
              memℒp_of_bounded (hμ h) (AEMeasurable.aestronglyMeasurable (hX.mono_ac hμ)) 2
          rw [p]
          simp only [Pi.pow_apply, mul_one]
          ring
      · rw [(by ext x; ring : (fun x ↦ -(A * (t - x) ^ 2 / 2)) =
          (fun x ↦ -A * ((x - t) ^ 2 / 2))),
            (by ring : (A * (t - x)) = -A * (x - t))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2 / 2) = (fun y ↦ (1 / 2) * (y - t) ^ 2)),
            (by ring : x - t = (1 / 2) * (2 * (x - t)))]
        apply HasDerivAt.const_mul
        rw [(by ext x; ring : (fun y ↦ (y - t) ^ 2) = (fun y ↦ y ^ 2 - 2 * t * y + t ^ 2)),
            (by ring : (2 * (x - t)) = 2 * (x ^ (2 - 1)) - 2 * t + 0)]
        apply HasDerivAt.add
        apply HasDerivAt.add
        apply hasDerivAt_pow
        rw [(by ext x; ring : (fun x ↦ -(2 * t * x)) = (fun x ↦ (x * -(2 * t))))]
        apply hasDerivAt_mul_const
        apply hasDerivAt_const
    have q4 : ∃ c ∈ (Set.Ioo 0 t), g' c = 0 := by
      apply exists_hasDerivAt_eq_zero (lt_of_le_of_ne ht fun a ↦ w (a.symm))
      apply HasDerivAt.continuousOn;
      intros x _; exact q3 x
      rw [q1, q2]
      intros x _; exact q3 x
    obtain ⟨c, ⟨cq, cq'⟩⟩ := q4
    intro
    use c; constructor
    · exact cq
    · dsimp only [g'] at cq';
      have cq'' : (A - f'' c) * (t - c) = 0 := by linarith
      have cq''' : A = f'' c := by
        have cr : (A - f'' c) = 0 := by
          simp only [mul_eq_zero] at cq''
          obtain cq''' | cq'''' := cq''
          · exact cq'''
          · dsimp only [Set.Ioo] at cq
            obtain ⟨_, cq2⟩ := cq
            linarith
        linarith
      rw [← cq''']
      exact q0
  rw [hf, hf'] at q
  simp only [Set.mem_Ioo, zero_mul, add_zero, zero_add, forall_const] at q
  obtain ⟨c, ⟨_, cq'⟩⟩ := q
  have s : f t ≤ t^2 * (b - a)^2 / 8 := by
    rw [cq']
    calc
    _ ≤ ((b - a) / 2) ^ 2 * t ^ 2 / 2 := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      dsimp [f'']
      have : IsProbabilityMeasure (μ.tilted fun ω ↦ t * X ω) :=
        isProbabilityMeasure_tilted (integrable_expt_bound μ hX h)
      exact tilt_var_bound μ a b c X h hX
      exact sq_nonneg t; simp only [inv_nonneg, Nat.ofNat_nonneg]
    _ = t ^ 2 * (b - a) ^ 2 / 8 := by ring
  exact s

/-! ### Hoeffding's lemma-/

/-- Hoeffding's Lemma states that for a random variable `X` with `E[X] = 0` (zero mean) and
 `a ≤ X ≤ b` almost surely, the inequality
 `μ[exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8)` holds almost surely for all `t ∈ ℝ`.-/
theorem hoeffding [IsProbabilityMeasure μ] (t a b : ℝ) (X : Ω → ℝ) (hX : AEMeasurable X μ)
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (h0 : μ[X] = 0) :
    μ[fun ω ↦ exp (t * (X ω))] ≤ exp (t^2 * (b - a)^2 / 8) := by
  by_cases h' : 0 ≤ t
  case pos =>
    exact hoeffding_nonneg μ t a b X h' hX h h0
  case neg =>
    simp only [not_le] at h'
    suffices ∫ ω, rexp (- t * - X ω) ∂μ ≤
      rexp ((- t) ^ 2 * ((- a) - (- b)) ^ 2 / 8) from by
      simp only [mul_neg, neg_mul, neg_neg, even_two, Even.neg_pow, sub_neg_eq_add] at this
      rw [<- (by ring : (-a + b) = b - a)]
      exact this
    apply hoeffding_nonneg _ _ _ _ _ (by linarith : 0 ≤ - t) (AEMeasurable.neg hX)
    · simp only [Set.mem_Icc, neg_le_neg_iff, Filter.eventually_and]
      exact ⟨h.mono fun ω h ↦ h.2, h.mono fun ω h ↦ h.1⟩
    · rw [integral_neg]
      simp only [neg_eq_zero]
      exact h0

end ProbabilityTheory
