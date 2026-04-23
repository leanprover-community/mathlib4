/-
Copyright (c) 2025 Yizheng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizheng Zhu
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Differentiation
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.NhdsWithin

/-!
# Lebesgue Differentiation Theorem (Interval Version)

This file proves the interval version of the Lebesgue Differentiation Theorem. There are two
versions in this file.

* `LocallyIntegrable.ae_hasDerivAt_integral` is the global version. It states that if `f : ℝ → ℝ`
  is locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
  `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.

* `IntervalIntegrable.ae_hasDerivAt_integral` is the local version. It states that if `f : ℝ → ℝ`
  is interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`,
  the derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`.
-/

public section

open MeasureTheory Set Filter Function IsUnifLocDoublingMeasure

open scoped Topology

/-- The (global) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is
locally integrable, then for almost every `x`, for any `c : ℝ`, the derivative of
`∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem LocallyIntegrable.ae_hasDerivAt_integral {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  have hg (x y : ℝ) : IntervalIntegrable f volume x y :=
    intervalIntegrable_iff.mpr <|
      (hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have LDT := (vitaliFamily volume 1).ae_tendsto_average hf
  have {a b : ℝ} : ∫ (t : ℝ) in Ioc a b, f t = ∫ (t : ℝ) in Icc a b, f t :=
    integral_Icc_eq_integral_Ioc (x := a) (y := b) (X := ℝ) |>.symm
  filter_upwards [LDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_ge, hy, this]
    grind
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    replace hy : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg,
        intervalIntegral.integral_of_le, hy, this]

/-- The (local) interval version of the *Lebesgue Differentiation Theorem*: if `f : ℝ → ℝ` is
interval integrable on `a..b`, then for almost every `x ∈ uIcc a b`, for any `c ∈ uIcc a b`, the
derivative of `∫ (t : ℝ) in c..x, f t` at `x` is equal to `f x`. -/
theorem IntervalIntegrable.ae_hasDerivAt_integral {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x, x ∈ uIcc a b → ∀ c ∈ uIcc a b, HasDerivAt (fun x => ∫ (t : ℝ) in c..x, f t) (f x) x := by
  wlog hab : a ≤ b
  · exact uIcc_comm b a ▸ @this f b a hf.symm (by linarith)
  rw [uIcc_of_le hab]
  have h₁ : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have h₂ : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g (x : ℝ) := if x ∈ Ioc a b then f x else 0
  have hg : LocallyIntegrable g volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hf.left
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg, h₁, h₂] with x hx _ _ _
  intro c hc
  #adaptation_note /-- 2025-09-30 https://github.com/leanprover/lean4/issues/10622
    `grind -order` calls used be `grind` -/
  refine HasDerivWithinAt.hasDerivAt (s := Ioo a b) ?_ <|
    Ioo_mem_nhds (by grind -order) (by grind -order)
  rw [show f x = g x by grind -order]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  all_goals apply intervalIntegral.integral_congr_ae' <;> filter_upwards <;> grind
