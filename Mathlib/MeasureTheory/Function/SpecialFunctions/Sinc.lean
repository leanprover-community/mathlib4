/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
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
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Measurability and integrability of the sinc function

## Main statements

* `measurable_sinc`: the sinc function is measurable.
* `integrable_sinc`: the sinc function is integrable with respect to any finite measure on `ℝ`.

-/

public section

open MeasureTheory

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : Measure α}

namespace Real

@[fun_prop]
lemma measurable_sinc : Measurable sinc := continuous_sinc.measurable

@[fun_prop]
lemma stronglyMeasurable_sinc : StronglyMeasurable sinc := measurable_sinc.stronglyMeasurable

@[fun_prop]
lemma integrable_sinc {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Integrable sinc μ := by
  refine Integrable.mono' (g := fun _ ↦ 1) (by fun_prop) (by fun_prop) <| ae_of_all _ fun x ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

end Real

open Real

@[fun_prop]
protected theorem Measurable.sinc (hf : Measurable f) : Measurable fun x ↦ sinc (f x) :=
  Real.measurable_sinc.comp hf

@[fun_prop]
protected theorem AEMeasurable.sinc (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ sinc (f x)) μ :=
  Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop]
protected theorem MeasureTheory.StronglyMeasurable.sinc (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x ↦ sinc (f x) :=
  Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop]
protected theorem MeasureTheory.AEStronglyMeasurable.sinc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ sinc (f x)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc
