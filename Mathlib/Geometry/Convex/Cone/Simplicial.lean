/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# Simplicial cones

A **simplicial cone** is a pointed convex cone that equals the conic span of a finite linearly
independent set of vectors. We do not require that the generators span the ambient module.
However, when the cone is also generating, its generators linearly span the module.

## Main definitions

* `PointedCone.IsSimplicial`: A pointed cone is simplicial if it equals the conic span of a finite
  linearly independent set.

## Results

* `PointedCone.IsSimplicial.span`: The conic span of a linearly independent finite set is
  simplicial.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

@[expose] public section

variable {R M : Type*}
variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid M] [Module R M]
variable (C : PointedCone R M)

namespace PointedCone

/-- A pointed cone is simplicial if it equals the conic span of a finite set that is linearly
independent over `R`. -/
def IsSimplicial : Prop :=
  ∃ s : Set M, s.Finite ∧ LinearIndepOn R id s ∧ span R s = C

namespace IsSimplicial

/-- The conic span of a finite linearly independent set is simplicial. -/
protected theorem span {s : Set M} (hs : s.Finite) (hli : LinearIndepOn R id s) :
    (PointedCone.span R s).IsSimplicial := ⟨s, hs, hli, rfl⟩

end IsSimplicial

end PointedCone
