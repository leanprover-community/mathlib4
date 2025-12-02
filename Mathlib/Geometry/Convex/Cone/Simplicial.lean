/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finitely generated and simplicial cones

This module introduces finiteness conditions for pointed cones, in
particular finitely generated cones and simplicial cones.

A cone is **finitely generated** if it is the conic hull (span over `R≥0`)
of a finite set of module elements (generators).

A **simplicial cone** is the conic hull of a finite set of vectors that are
linearly independent over the ring R.

Geometrically, a simplicial cone is a cone over a simplex.

## Definitions

* `PointedCone.FG`: A pointed cone is finitely generated if it is the conic hull of
a finite set.
* `PointedCone.Simplicial`: A pointed cone is simplicial if it equals the conic hull of
  a finite set that is linearly independent over `R`.

## Lemmas

* `PointedCone.simplicial_bot`: The zero cone is simplicial.
* `PointedCone.Simplicial.fg`: A simplicial pointed cone is finitely generated.

## Notation

* We use a local notation `R≥0` for the semiring of nonnegative scalars `{c : R // 0 ≤ c}`.

## Implementation notes

* A pointed cone is defined as a submodule over the semiring of nonnegative scalars
  `R≥0` and we reuse the `Submodule.FG` API.
* Polyhedral cones are more complex and are postponed for later additions.
* Terminology: Simplicial cones are sometimes called simplex cones.

## References

-/

@[expose] public section

namespace PointedCone

variable {R M : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]

local notation3 "R≥0" => {c : R // 0 ≤ c}

/-- A pointed cone is finitely generated if it is the conic hull of a finite set. -/
def FG (C : PointedCone R M) : Prop := Submodule.FG C

/-- A pointed cone is simplicial if it equals the conic hull of
  a finite set that is linearly independent over `R`. -/
def Simplicial (C : PointedCone R M) : Prop :=
  ∃ s : Set M, s.Finite ∧ LinearIndependent R (fun x : s => (x : M)) ∧ span R s = C

/-- The zero cone is simplicial. -/
theorem simplicial_bot : (⊥ : PointedCone R M).Simplicial :=
  ⟨∅, Set.finite_empty, linearIndependent_empty_type, by simp [Submodule.span_empty]⟩

/-- A simplicial pointed cone is finitely generated. -/
theorem Simplicial.fg {C : PointedCone R M} (hC : C.Simplicial) : C.FG :=
  let ⟨s, hsfin, _, hspan⟩ := hC
  Submodule.fg_def.mpr ⟨s, hsfin, hspan⟩

end PointedCone
