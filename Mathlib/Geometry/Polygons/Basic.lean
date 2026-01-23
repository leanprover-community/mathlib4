/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine

/-!
# Polygons

This file defines polygons in a module over ℝ.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a module `P` over `ℝ`.
* `EuclideanPolygon n`: A polygon in 2-dimensional Euclidean space.
* `Polygon.edgeSet i`: The `i`-th edge as a set (line segment between consecutive vertices).
* `Polygon.edgePath i`: The `i`-th edge as a parametric path.
* `Polygon.boundary`: The boundary of the polygon (union of all edges).

## Main theorems

* `Polygon.edgeSet_eq_image`: The edge set equals the image of the edge path on `[0, 1]`.

-/

open Set Topology

/-- A polygon with `n` vertices in a module `P` over `ℝ`. -/
structure Polygon (P : Type*) (n : ℕ) [NeZero n] [AddCommGroup P] [Module ℝ P] where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n → P


/-- A polygon in 2-dimensional Euclidean space. -/
structure EuclideanPolygon (n : ℕ) [NeZero n] : Type where
  toPolygon : Polygon (EuclideanSpace ℝ (Fin 2)) n
  /-- In Euclidean space, polygons must have at least 3 vertices. -/
  n_ge_3 : 3 ≤ n

namespace Polygon

variable {P : Type*} {n : ℕ} [NeZero n]
variable [AddCommGroup P] [Module ℝ P]

/-- The `i`-th edge of the polygon as a set (line segment from vertex `i` to vertex `i + 1`). -/
def edgeSet (poly : Polygon P n) (i : Fin n) : Set P :=
  segment ℝ (poly.vertices i) (poly.vertices (i + 1))

/-- The `i`-th edge of the polygon as a parametric path using `AffineMap.lineMap`. -/
def edgePath (poly : Polygon P n) (i : Fin n) : ℝ → P :=
  AffineMap.lineMap (poly.vertices i) (poly.vertices (i + 1))

/-- The boundary of the polygon is the union of all its edges. -/
def boundary (poly : Polygon P n) : Set P := ⋃ i, poly.edgeSet i

/-- The edge set equals the image of the edge path on the unit interval. -/
theorem edgeSet_eq_image (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet i = poly.edgePath i '' Icc (0 : ℝ) 1 := by
  simp only [edgeSet, edgePath, segment_eq_image_lineMap]

end Polygon
