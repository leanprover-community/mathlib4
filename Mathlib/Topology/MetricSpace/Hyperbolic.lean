/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.GromovProduct
/-!

# Gromov hyperbolic pseudometric spaces

## Main definitions

* `IsHyperbolicWith`: A pseudometric space is hyperbolic with constant `δ`
if and only if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds.
* `IsHyperbolic`: A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some constant `δ`.

## Main results

* `isHyperbolic_of_boundedSpace`: A bounded space is δ-hyperbolic with respect to its diameter.

## Implementation notes

The constant `δ` in `IsHyperbolicWith X δ` is a real number, and the definition does not ask for
`0 ≤ δ`. Taking `w = x = y = z` in the four-point condition, the condition reads `-δ ≤ 0`.

## Tags

Gromov hyperbolic pseudometric space
-/

@[expose] public section

namespace Metric

/-- A pseudometric space is hyperbolic with constant `δ`
if and only if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds. -/
def IsHyperbolicWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ w x y z : X, min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z

/-- A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some real constant `δ`. -/
class IsHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop where
  exists_isHyperbolicWith : ∃ δ, IsHyperbolicWith X δ

variable {X : Type*} [PseudoMetricSpace X]

@[grind .]
lemma isHyperbolicWith_of_forall_dist_le {k : ℝ} (hk : ∀ x y : X, dist x y ≤ k) :
    IsHyperbolicWith X k := by
  grind [IsHyperbolicWith, gromovProduct_le_dist_left]

/-- A bounded space is δ-hyperbolic with respect to its diameter. -/
theorem isHyperbolicWith_diam_univ [BoundedSpace X] :
    IsHyperbolicWith X (diam (Set.univ : Set X)) := by
  grind [dist_le_diam_of_mem]

instance [BoundedSpace X] : IsHyperbolic X := ⟨_, isHyperbolicWith_diam_univ⟩

end Metric
