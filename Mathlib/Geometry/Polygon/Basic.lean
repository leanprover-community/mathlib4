/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Topology.Algebra.Affine
public import Mathlib.Algebra.Ring.Defs

/-!
# Polygons

This file defines polygons in affine spaces.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a type `P`.

-/

@[expose] public section

open Set

/-- A polygon with `n` vertices in a type `P`. -/
structure Polygon (P : Type*) (n : ℕ) where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n → P

namespace Polygon

variable {R V P : Type*} {n : ℕ}

/-- A coercion to function so that vertices can
be written as `poly i` instead of `poly.vertices i` -/
instance : CoeFun (Polygon P n) (fun _ => Fin n → P) where
  coe := Polygon.vertices

variable (R)
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [NeZero n]

/-- The `i`-th edge as an affine map `R →ᵃ[R] P`. -/
def edgePath (poly : Polygon P n) (i : Fin n) : R →ᵃ[R] P :=
  AffineMap.lineMap (poly i) (poly (i + 1))

/-- The `i`-th edge as a set of points using an `affineSegment`. -/
def edgeSet [PartialOrder R]
    (poly : Polygon P n) (i : Fin n) : Set P :=
  affineSegment R (poly i) (poly (i + 1))

/-- The `edgeSet` is equivalent to the image of the `edgePath`. -/
theorem edgeSet_eq_image_edgePath [PartialOrder R]
    (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet R i = poly.edgePath R i '' Icc (0 : R) 1 := rfl

/-- The boundary of the polygon is the union of all its edges. -/
def boundary [PartialOrder R] (poly : Polygon P n) : Set P :=
  ⋃ i, poly.edgeSet R i

end Polygon
