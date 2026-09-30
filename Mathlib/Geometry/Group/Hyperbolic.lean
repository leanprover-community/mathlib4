/-
Copyright (c) 2026 Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
module

public import Mathlib.Geometry.Group.WordMetric
public import Mathlib.Topology.MetricSpace.Hyperbolic

/-!
# Hyperbolic groups

A finitely generated group is hyperbolic if its induced metric space with respect to a chosen family
of `Group.Generators` satisfies the Gromov hyperbolicity condition.

## Main definitions

* `Generators.IsHyperbolicWith`: A group is `δ`-hyperbolic with respect to a generating set `P`
  if its induced metric space is `δ`-hyperbolic.
* `IsHyperbolic`: A group `G` is hyperbolic if there exists a finite generating family `P` and a
  constant `δ` such that `G` is δ-hyperbolic with respect to `P`.

## Main results

* `[IsHyperbolic G] : FG G`: Every hyperbolic group is finitely generated.
* `[Finite G] : IsHyperbolic G`: Every finite group is hyperbolic.

## Implementation notes

The hyperbolicity condition applies directly to the word metric, without requiring the Cayley graph.

## Tags

hyperbolic group
-/

@[expose] public section

namespace Group

variable {G ι : Type*} [Group G]

/-- A group is `δ`-hyperbolic with respect to a generating set `P` if its induced metric space is
`δ`-hyperbolic. -/
def Generators.IsHyperbolicWith (P : Generators G ι) (δ : ℝ) : Prop :=
  letI := P.normedGroup
  Metric.IsHyperbolicWith G δ

/-- A group `G` is hyperbolic if there exists a finite generating family `P` and a constant `δ` such
that `G` is δ-hyperbolic with respect to `P`. -/
class IsHyperbolic (G : Type*) [Group G] : Prop where
  exists_isHyperbolicWith (G) : ∃ (n : ℕ) (P : Generators G (Fin n)) (δ : ℝ), P.IsHyperbolicWith δ

/-- Every hyperbolic group is finitely generated. -/
instance [IsHyperbolic G] : FG G := by
  obtain ⟨_, P, _, _⟩ := IsHyperbolic.exists_isHyperbolicWith G
  exact P.fg

set_option trace.Meta.synthInstance true in
/-- Every finite group is hyperbolic. -/
instance [Finite G] : IsHyperbolic G :=
  let ⟨n, ⟨P⟩⟩ := fg_iff_nonempty_finite_generators.mp inferInstance
  ⟨n, P, Metric.IsHyperbolic.exists_isHyperbolicWith⟩

end Group
