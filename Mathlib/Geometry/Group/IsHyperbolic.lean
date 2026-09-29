/-
Copyright (c) Hang Lu Su, Katerina Hristova. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Katerina Hristova
-/
module

public import Mathlib.Geometry.Group.WordMetric
public import Mathlib.Topology.MetricSpace.Hyperbolic

/-!
# Hyperbolic groups

## Main definitions

`Generators.IsHyperbolicWith`:

## Implementation notes

The hyperbolicity condition applies directly to the word metric, without requiring the Cayley graph.

## Tags

hyperbolic group
-/

@[expose] public section

namespace Group

variable {G ι : Type*} [Group G]

/-- A group is δ-hyperbolic with respect to a generating set `P` if its induced metric space is
δ-hyperbolic. -/
def Generators.IsHyperbolicWith (P : Generators G ι) (δ : ℝ) : Prop :=
  letI := P.normedGroup
  Metric.IsHyperbolicWith G δ

/-- A group `G` is hyperbolic if there exists a finite generating family `P` and a constant `δ` such
that `G` is δ-hyperbolic with respect to `P`. -/
class IsHyperbolic (G : Type*) [Group G] : Prop where
/-- A finite generating family whose induced metric space is hyperbolic. -/
  exists_isHyperbolicWith (G) : ∃ (n : ℕ) (P : Generators G (Fin n)) (δ : ℝ), P.IsHyperbolicWith δ

/-- Every hyperbolic group is finitely generated. -/
instance [IsHyperbolic G] : FG G := by
  obtain ⟨n, P, δ, hP⟩ := IsHyperbolic.exists_isHyperbolicWith G
  exact P.fg

/-- Every finite group is hyperbolic. -/
instance [Finite G] : IsHyperbolic G := by
  obtain ⟨n, ⟨P⟩⟩ := (Group.fg_iff_nonempty_finite_generators (G := G)).mp inferInstance
  exact ⟨n, P, Metric.IsHyperbolic.exists_isHyperbolicWith⟩

end Group
