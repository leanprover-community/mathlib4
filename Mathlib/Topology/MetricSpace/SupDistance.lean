/-
Copyright (c) 2025 Julien Michel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julien Michel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Tactic.Finiteness

/-!
# Supremal distance to a set

This file defines and studies the supremal distance in pseudo (extended) metric spaces.
Given a point `x` and a set `s` in a metric space, the supremal distance from `x` to `s` is
defined as the supremum of the distances from `x` to the points in `s`.
This quantity can be infinite in emetric spaces.

## Main definitions

- `EMetric.supEdist` : the supremal extended distance from a point to a set.
- `Metric.supDist` : the supremal distance from a point to a set.

## Main results


-/

@[expose] public section

section SupEdist

open ENNReal

universe u

variable {α : Type u} [PseudoEMetricSpace α]

namespace EMetric

/-! ### Supremal distance of a point to a set as a function into `ℝ≥0∞`. -/

/-- The supremal edistance of a point to a set -/
noncomputable def supEdist (x : α) (s : Set α) : ℝ≥0∞ := ⨆ y ∈ s, edist x y

end EMetric

end SupEdist

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

section SupDist

open ENNReal EMetric

universe u

variable {α : Type u} [PseudoMetricSpace α]

namespace Metric

/-! ### Supremal distance of a point to a set as a function into `ℝ`. -/

/-- The supremal distance of a point to a set -/
noncomputable def supDist (x : α) (s : Set α) : ℝ := (supEdist x s).toReal

end Metric

end SupDist
