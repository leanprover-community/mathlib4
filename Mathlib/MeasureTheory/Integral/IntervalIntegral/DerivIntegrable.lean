/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Batteries.Tactic.Congr
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Slope
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin

/-!
# `f'` is interval integrable for certain classes of functions `f`

This file proves that:
* `MonotoneOn.intervalIntegrable_deriv`: If `f` is monotone on `a..b`, then `f'` is interval
  integrable on `a..b`.
* `MonotoneOn.intervalIntegral_deriv_mem_uIcc`: If `f` is monotone on `a..b`, then the integral of
  `f'` on `a..b` is in `uIcc 0 (f b - f a)`.
* `BoundedVariationOn.intervalIntegrable_deriv`: If `f` has bounded variation on `a..b`,
  then `f'` is interval integrable on `a..b`.
* `AbsolutelyContinuousOnInterval.intervalIntegrable_deriv`: If `f` is absolutely continuous on
  `a..b`, then `f'` is interval integrable on `a..b`.

## Tags
interval integrable, monotone, bounded variation, absolutely continuous
-/

public section

open MeasureTheory Set Filter

open scoped Topology

/-- If `f` is monotone on `[a, b]`, then `f'` is the limit of `G n` a.e. on `[a, b]`, where each
`G n` is `AEStronglyMeasurable` and the liminf of the lower Lebesgue integral of `‖G n ·‖ₑ` is at
most `f b - f a`. -/
lemma MonotoneOn.exists_tendsto_deriv_liminf_lintegral_enorm_le
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    ∃ G : (ℕ → ℝ → ℝ), (∀ᵐ x ∂volume.restrict (Icc a b),
      Filter.Tendsto (fun (n : ℕ) ↦ G n x) Filter.atTop (𝓝 (deriv f x))) ∧
      (∀ (n : ℕ), AEStronglyMeasurable (G n) (volume.restrict (Icc a b))) ∧
      liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≤
        ENNReal.ofReal (f b - f a) := by
  /- Proof Sketch: Extend `f` on `[a, b]` to a function `g` on `ℝ` by defining `g x = f a` for
  `x < a` and `g x = f b` for `x > b`. `g` is globally monotone and `g'` agrees with `f'` on
  `(a, b)`. We let `G c x = slope g x (x + c)` for `c > 0`. Then `G c x` is nonnegative,
  `∫⁻ (x : ℝ) in Icc a b, ‖G c x‖ₑ ≤ f b - f a`, and `G c x` tends to `f' x` as `c` tends to `0`
  from the right. The function `fun n x ↦ G (n : ℝ)⁻¹ x` is a witness to the conclusion of the
  lemma. -/
  let g (x : ℝ) : ℝ := f (max a (min x b))
  have hg : Monotone g := monotoneOn_univ.mp <| hf.comp (by grind [MonotoneOn]) (by grind [MapsTo])
  have hfg : EqOn f g (Ioo a b) := by grind [EqOn]
  replace hfg := hfg.deriv isOpen_Ioo
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let G (c x : ℝ) := slope g x (x + c)
  have G_integrable (n : ℕ) : Integrable (G (↑n)⁻¹) (volume.restrict (Icc a b)) := by
    have := hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegrable_slope hab (by simp)
    exact intervalIntegrable_iff_integrableOn_Icc_of_le hab |>.mp this
  refine ⟨fun n x ↦ G (n : ℝ)⁻¹ x, ?_, fun n ↦ G_integrable n |>.aestronglyMeasurable, ?_⟩
  · rw [MeasureTheory.ae_restrict_iff' (by measurability)]
    filter_upwards [hg.ae_differentiableAt, h₁, h₂] with x hx₁ hx₂ hx₃ hx₄
    rw [hfg (by grind [Icc_diff_both])]
    exact hx₁.hasDerivAt.tendsto_slope.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by convert tendsto_const_nhds.add (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)); simp)
      (by simp [eventually_ne_atTop 0])
  · calc
      _ = liminf (fun (n : ℕ) ↦ ENNReal.ofReal (∫ (x : ℝ) in Icc a b, (G (n : ℝ)⁻¹) x)) atTop := by
        apply Filter.liminf_congr
        filter_upwards with n
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (G_integrable n)]
        congr with y
        exact abs_eq_self.mpr (hg.monotoneOn univ |>.slope_nonneg trivial trivial)
      _ ≤ ENNReal.ofReal (g b - g a) := by
        refine Filter.liminf_le_of_frequently_le'
          (Filter.Frequently.of_forall fun n ↦ ENNReal.ofReal_le_ofReal ?_)
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
        convert hg.monotoneOn (Icc a (b + (n : ℝ)⁻¹)) |>.intervalIntegral_slope_le hab (by simp)
          using 2
        simp [g]
      _ = ENNReal.ofReal (f b - f a) := by grind

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b`. -/
theorem MonotoneOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  wlog hab : a ≤ b generalizing a b with h
  · exact h (uIcc_comm a b ▸ hf) (by linarith) |>.symm
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have hG'₀ : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≠ ⊤ :=
    lt_of_le_of_lt hG' ENNReal.ofReal_lt_top |>.ne_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr integrable_f_deriv

/-- If `f` is monotone on `a..b`, then `f'` is interval integrable on `a..b` and the integral of
`f'` on `a..b` is in between `0` and `f b - f a`. -/
theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (uIcc a b)) :
    ∫ x in a..b, deriv f x ∈ uIcc 0 (f b - f a) := by
  wlog hab : a ≤ b generalizing a b with h
  · specialize h (uIcc_comm a b ▸ hf) (by linarith)
    have : f b ≤ f a := hf (by simp) (by simp) (by linarith)
    rw [intervalIntegral.integral_symm, uIcc_of_ge (by linarith)]
    refine neg_mem_Icc_iff.mpr ?_
    simp only [neg_zero, neg_sub]
    rwa [uIcc_of_le (by linarith)] at h
  rw [uIcc_of_le hab] at hf
  obtain ⟨G, hGf, hG, hG'⟩ := hf.exists_tendsto_deriv_liminf_lintegral_enorm_le hab
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  have hG'₀ : liminf (fun (n : ℕ) ↦ ∫⁻ (x : ℝ) in Icc a b, ‖G n x‖ₑ) atTop ≠ ⊤ :=
    lt_of_le_of_lt hG' ENNReal.ofReal_lt_top |>.ne_top
  have integrable_f_deriv := integrable_of_tendsto hGf hG hG'₀
  rw [MeasureTheory.ae_restrict_iff' (by simp)] at hGf
  rw [← uIcc_of_le hab] at hGf hG hG'
  have : f a ≤ f b := hf (by simp [hab]) (by simp [hab]) hab
  rw [uIcc_of_le (by linarith), mem_Icc]
  have f_deriv_nonneg {x : ℝ} (hx : x ∈ Ioo a b) : 0 ≤ deriv f x := by
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds (a := a) (b := b) (by grind) (by grind))]
    exact hf.derivWithin_nonneg
  constructor
  · apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff' (by simp)]
    filter_upwards [h₁, h₂] with x _ _ _
    exact f_deriv_nonneg (by grind [Icc_diff_both])
  · have ebound := lintegral_enorm_le_liminf_of_tendsto
      ((MeasureTheory.ae_restrict_iff' (by measurability) |>.mpr hGf))
      (fun n ↦ (hG n).aemeasurable.enorm)
    grw [hG'] at ebound
    rw [uIcc_of_le hab,
        ← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm integrable_f_deriv,
        ENNReal.ofReal_le_ofReal_iff (by linarith),
        integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab] at ebound
    convert ebound using 1
    refine intervalIntegral.integral_congr_ae ?_
    rw [uIoc_of_le hab]
    filter_upwards [h₂] with x _ _
    exact abs_eq_self.mpr (f_deriv_nonneg (by grind)) |>.symm

/-- If `f` has bounded variation on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem BoundedVariationOn.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  obtain ⟨p, q, hp, hq, rfl⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  have h₂ : ∀ᵐ x, x ≠ max a b := by simp [ae_iff, measure_singleton]
  apply (hp.intervalIntegrable_deriv.sub hq.intervalIntegrable_deriv).congr_ae
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' (by simp [uIoc])]
  filter_upwards [hp.ae_differentiableWithinAt_of_mem, hq.ae_differentiableWithinAt_of_mem, h₂]
    with x hx₁ hx₂ hx₃ hx₄
  have hx₅ : x ∈ uIcc a b := Ioc_subset_Icc_self hx₄
  rw [uIoc, mem_Ioc] at hx₄
  have hx₆ : uIcc a b ∈ 𝓝 x := Icc_mem_nhds hx₄.left (lt_of_le_of_ne hx₄.right hx₃)
  replace hx₁ := (hx₁ hx₅).differentiableAt hx₆ |>.hasDerivAt
  replace hx₂ := (hx₂ hx₅).differentiableAt hx₆ |>.hasDerivAt
  exact (hx₁.sub hx₂).deriv.symm

/-- If `f` is absolutely continuous on `uIcc a b`, then `f'` is interval integrable on `a..b`. -/
theorem AbsolutelyContinuousOnInterval.intervalIntegrable_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.boundedVariationOn.intervalIntegrable_deriv
