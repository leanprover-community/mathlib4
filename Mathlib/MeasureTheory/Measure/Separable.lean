/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Separable measures

## Main definitions

* `IsSeparable`: A measure `μ` is separable if there is a separable set `S` such that
  `μ S = μ Set.univ`.

## Main statements

*

## Notation


## Implementation details

-/

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- A measure `μ` is separable if there is a separable set `S` such that `μ S = μ Set.univ`. -/
def IsSeparable [TopologicalSpace α] (μ : Measure α) : Prop :=
  ∃ S : Set α, TopologicalSpace.IsSeparable S ∧ μ S = μ Set.univ

namespace IsSeparable

end IsSeparable
end MeasureTheory
