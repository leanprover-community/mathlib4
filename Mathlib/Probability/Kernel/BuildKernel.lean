/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.StieltjesReal
import Mathlib.Probability.Kernel.Basic

/-!


-/


open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace ProbabilityTheory

variable {α : Type*} [MeasurableSpace α] {f : α → ℚ → ℝ} {hf : ∀ q, Measurable fun a ↦ f a q}

noncomputable
def cdfKernel (hf : ∀ q, Measurable fun a ↦ f a q) : kernel α ℝ where
  val a := (todo3 f hf a).measure
  property := measurable_measure_todo3 hf

instance instIsMarkovKernel_cdfKernel : IsMarkovKernel (cdfKernel hf) :=
  ⟨fun _ ↦ instIsProbabilityMeasure_todo3 _ _⟩

lemma cdfKernel_Iic (a : α) (x : ℝ) :
    cdfKernel hf a (Iic x) = ENNReal.ofReal (todo3 f hf a x) := measure_todo3_Iic hf a x

end ProbabilityTheory
