/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.GromovProduct
public import Mathlib.Topology.MetricSpace.Isometry
/-!

# Gromov hyperbolic pseudometric spaces

## Main definitions

* `IsHyperbolicWith`: A pseudometric space is hyperbolic with constant `δ`
if and only if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds.
* `IsHyperbolic`: A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some constant `δ`.

## Main results

* `IsHyperbolicWith.of_isometry`: A space with an isometry into a `δ`-hyperbolic space is also
  `δ`-hyperbolic.
* `IsHyperbolicWith.subtype`: A subspace of a δ-hyperbolic space is `δ`-hyperbolic.
* `isHyperbolicWith_diam_univ`: A bounded space is `δ`-hyperbolic with respect to its diameter.

## Implementation notes

The constant `δ` in `IsHyperbolicWith X δ` is a real number. For a non-empty space,
taking `w = x = y = z` in the four-point condition yields `0 ≤ δ`.

## Tags

Gromov hyperbolic pseudometric space
-/

@[expose] public section

namespace Metric

/-! ### δ-hyperbolic spaces -/

/-- A pseudometric space is `δ`-hyperbolic if for all `w x y z` the four-point condition
`min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z` holds. -/
@[wikidata Q3828581]
def IsHyperbolicWith (X : Type*) [PseudoMetricSpace X] (δ : ℝ) : Prop :=
  ∀ w x y z : X, min (gromovProduct w x y) (gromovProduct w y z) - δ ≤ gromovProduct w x z

variable {X Y : Type*} {δ δ' : ℝ} [PseudoMetricSpace X] [PseudoMetricSpace Y]

namespace IsHyperbolicWith

/-- If a space is δ-hyperbolic, and δ ≤ δ', then it is also δ'-hyperbolic. -/
@[grind →]
lemma mono (h : IsHyperbolicWith X δ) (hδ : δ ≤ δ') : IsHyperbolicWith X δ' := by
  grind [IsHyperbolicWith]

/-- A non-empty space being δ-hyperbolic implies that 0 ≤ δ. -/
@[grind →]
lemma nonneg [hX : Nonempty X] (h : IsHyperbolicWith X δ) : 0 ≤ δ := by
  obtain ⟨x⟩ := hX
  grind [h x x x x]

/-- A space with an isometry into a `δ`-hyperbolic space is also `δ`-hyperbolic. -/
@[grind →]
theorem of_isometry {f : X → Y} (h : IsHyperbolicWith Y δ) (hf : Isometry f) :
    IsHyperbolicWith X δ := by
  intro w x y z
  grind [h (f w) (f x) (f y) (f z), gromovProduct_eq, Isometry.dist_eq]

/-- A subspace of a δ-hyperbolic space is δ-hyperbolic. -/
@[grind .]
theorem subtype (h : IsHyperbolicWith X δ) (p : X → Prop) : IsHyperbolicWith (Subtype p) δ :=
  h.of_isometry isometry_subtype_coe

end IsHyperbolicWith

/-- A pseudometric space with all distances bounded above by `k` is `k`-hyperbolic. -/
@[grind .]
lemma isHyperbolicWith_of_forall_dist_le {k : ℝ} (hk : ∀ x y : X, dist x y ≤ k) :
    IsHyperbolicWith X k := by
  grind [IsHyperbolicWith, gromovProduct_le_dist_left]

/-- A bounded space is δ-hyperbolic with respect to its diameter. -/
theorem isHyperbolicWith_diam_univ [BoundedSpace X] :
    IsHyperbolicWith X (diam (Set.univ : Set X)) := by
  grind [dist_le_diam_of_mem]

/-! ### Hyperbolic spaces -/

/-- A pseudometric space is hyperbolic if it is `δ`-hyperbolic for some real constant `δ`. -/
class IsHyperbolic (X : Type*) [PseudoMetricSpace X] : Prop where
  exists_isHyperbolicWith : ∃ δ, IsHyperbolicWith X δ

/-- Every bounded pseudometric space is hyperbolic. -/
instance [BoundedSpace X] : IsHyperbolic X := ⟨_, isHyperbolicWith_diam_univ⟩

/-- A subspace of a hyperbolic space is hyperbolic. -/
instance [h : IsHyperbolic X] (p : X → Prop) : IsHyperbolic (Subtype p) := by
  obtain ⟨_, hX⟩ := h
  exact ⟨_, hX.subtype p⟩

end Metric
