/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
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
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive

/-!
# Bochner integrals of convolutions

This file contains results about the Bochner integrals of convolutions of measures.

These results are not placed in the main convolution file because we don't want to import Bochner
integrals over there.

## Main statements

* `integrable_conv_iff`: A function is integrable with respect to the convolution `μ ∗ ν` iff
  the function `y ↦ f (x + y)` is integrable with respect to `ν` for `μ`-almost every `x` and
  the function `x ↦ ∫ y, ‖f (x + y)‖ ∂ν` is integrable with respect to `μ`.
* `integral_conv`: if `f` is integrable with respect to the convolution `μ ∗ ν`, then
  `∫ x, f x ∂(μ ∗ₘ ν) = ∫ x, ∫ y, f (x + y) ∂ν ∂μ`.
-/

public section

namespace MeasureTheory

variable {M F : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
  [NormedAddCommGroup F] {μ ν : Measure M} {f : M → F}

@[to_additive]
lemma integrable_mconv_iff [SFinite ν] (hf : AEStronglyMeasurable f (μ ∗ₘ ν)) :
    Integrable f (μ ∗ₘ ν)
      ↔ (∀ᵐ x ∂μ, Integrable (fun y ↦ f (x * y)) ν)
        ∧ Integrable (fun x ↦ ∫ y, ‖f (x * y)‖ ∂ν) μ := by
  simp [Measure.mconv, integrable_map_measure hf (by fun_prop),
    integrable_prod_iff (hf.comp_measurable (by fun_prop))]

@[to_additive]
lemma integral_mconv [NormedSpace ℝ F] [SFinite μ] [SFinite ν] (hf : Integrable f (μ ∗ₘ ν)) :
    ∫ x, f x ∂(μ ∗ₘ ν) = ∫ x, ∫ y, f (x * y) ∂ν ∂μ := by
  unfold Measure.mconv
  rw [integral_map (by fun_prop) hf.1, integral_prod]
  exact (integrable_map_measure hf.1 (by fun_prop)).mp hf

end MeasureTheory
