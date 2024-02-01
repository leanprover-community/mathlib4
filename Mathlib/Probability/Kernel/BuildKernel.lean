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

variable {α : Type*} [MeasurableSpace α]

noncomputable
def IsCDFLike.kernel {f : α → ℚ → ℝ} (hf : IsCDFLike f) : kernel α ℝ where
  val (a : α) := (todo2 hf a).measure
  property := measurable_measure_todo2 hf

end ProbabilityTheory
