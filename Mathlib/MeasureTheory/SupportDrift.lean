/-
Copyright (c) 2026 Inacio Vasquez.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Inacio Vasquez
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support Drift for Probability Measures
-/

namespace MeasureTheory

open Set

variable {α : Type*}
variable [TopologicalSpace α]
variable [MeasurableSpace α]

noncomputable def supportDrift (μ ν : ProbabilityMeasure α) : Set α :=
  (Measure.support μ.toMeasure \ Measure.support ν.toMeasure) ∪
  (Measure.support ν.toMeasure \ Measure.support μ.toMeasure)

end MeasureTheory
