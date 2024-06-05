/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.QuasiSeparated

/-!

# Proper morphisms

A morphism of schemes is proper if is of finite type, separated and universally closed.

## TODO

- Show proper is stable under composition and base change.
- Show proper is local at the target.

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism is proper if it is of finite type, separated and universally closed . -/
@[mk_iff]
class IsProper (f : X ⟶ Y) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f := by infer_instance
  quasiCompact : QuasiCompact f := by infer_instance
  universallyClosed : UniversallyClosed f := by infer_instance
  isSeparated : IsSeparated f := by infer_instance

namespace IsProper

instance [IsIso f] : IsProper f where

end IsProper

end AlgebraicGeometry
