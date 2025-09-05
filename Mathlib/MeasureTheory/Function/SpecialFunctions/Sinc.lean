/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Measurability and integrability of the sinc function

## Main statements

* `measurable_sinc`: the sinc function is measurable.
* `integrable_sinc`: the sinc function is integrable with respect to any finite measure on `ℝ`.

-/

open MeasureTheory

variable {α : Type*} {_ : MeasurableSpace α} {f : α → ℝ} {μ : Measure α}

namespace Real

@[fun_prop, measurability]
lemma measurable_sinc : Measurable sinc := continuous_sinc.measurable

@[fun_prop, measurability]
lemma stronglyMeasurable_sinc : StronglyMeasurable sinc := measurable_sinc.stronglyMeasurable

@[fun_prop]
lemma integrable_sinc {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Integrable sinc μ := by
  refine Integrable.mono' (g := fun _ ↦ 1) (by fun_prop) (by fun_prop) <| ae_of_all _ fun x ↦ ?_
  rw [Real.norm_eq_abs]
  exact abs_sinc_le_one x

end Real

open Real

@[fun_prop, measurability]
protected theorem Measurable.sinc (hf : Measurable f) : Measurable fun x ↦ sinc (f x) :=
  Real.measurable_sinc.comp hf

@[fun_prop, measurability]
protected theorem AEMeasurable.sinc (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ sinc (f x)) μ :=
  Real.measurable_sinc.comp_aemeasurable hf

@[fun_prop, measurability]
protected theorem MeasureTheory.StronglyMeasurable.sinc (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x ↦ sinc (f x) :=
  Real.stronglyMeasurable_sinc.comp_measurable hf.measurable

@[fun_prop, measurability]
protected theorem MeasureTheory.AEStronglyMeasurable.sinc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x ↦ sinc (f x)) μ := by
  rw [aestronglyMeasurable_iff_aemeasurable] at hf ⊢
  exact hf.sinc
