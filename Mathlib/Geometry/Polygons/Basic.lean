/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Affine
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Polygons

This file defines polygons in general, Euclidean polygons in 2D space,
and triangles as Euclidean polygons.

## Main definitions

* `Polygon P n`: A polygon with `n` vertices in a type `P`.
* `EuclideanPolygon n`: A polygon with `n` vertices with `n ≥ 3` in 2-dimensional Euclidean space.
* `EuclideanTriangle`: A non-degenerate triangle in 2D Euclidean space, compatible with
  `Affine.Triangle`.
* `Polygon.edgePath i`: The `i`-th edge as an affine map (for general affine spaces).
* `Polygon.edgeSet i`: The `i`-th edge as a set (line segment between consecutive vertices).
* `Polygon.edgePathModule i`: The `i`-th edge as an affine map (for real modules).
* `Polygon.side i`: The `i`-th edge as a real segment (for real modules).
* `Polygon.boundary`: The boundary of the polygon (union of all edges).
* `EuclideanPolygon.edgeLength`: The length of an edge as the distance between vertices.
* `EuclideanPolygon.interiorAngle`: The interior angle at a vertex.
* `EuclideanPolygon.perimeter`: The perimeter of a polygon.
* `EuclideanTriangle.toAffineTriangle`: Convert to `Affine.Triangle`.
* `EuclideanTriangle.ofAffineTriangle`: Convert from `Affine.Triangle`.

## Main theorems

* `Polygon.edgeSet_eq_image_edgePath`: The edge set equals the image of the edge path on `[0, 1]`.
* `Polygon.side_eq_edgeSet`: The side equals the affine edge set.

-/

open Set

/-- A polygon with `n` vertices in a type `P`. -/
structure Polygon (P : Type*) (n : ℕ) where
  /-- The vertices of the polygon, indexed by `Fin n`. -/
  vertices : Fin n → P

/-- A polygon with `n` vertices in 2-dimensional Euclidean space. -/
structure EuclideanPolygon (n : ℕ) : Type
    extends Polygon (EuclideanSpace ℝ (Fin 2)) n where
  /-- In Euclidean space, non-degenerate polygons must have at least 3 vertices. -/
  n_ge_3 : 3 ≤ n

/-- A Euclidean triangle is a non-degenerate triangle in 2D Euclidean space.
The `verticesNoncollinear` condition ensures the three vertices are affinely independent,
making this compatible with `Affine.Triangle`. -/
structure EuclideanTriangle extends EuclideanPolygon 3 where
  verticesNoncollinear : AffineIndependent ℝ vertices

namespace Polygon

section Affine



/-- The `i`-th edge as an affine map `ℝ →ᵃ[ℝ] P`. -/
def edgePath (poly : Polygon P n) (i : Fin n) : ℝ →ᵃ[ℝ] P :=
  AffineMap.lineMap (poly.vertices i) (poly.vertices (i + 1))

/-- The `i`-th edge as a set: the image of the `edgePath` map. -/
def edgeSet (poly : Polygon P n) (i : Fin n) : Set P :=
  poly.edgePath i '' Icc (0 : ℝ) 1

/-- The boundary of the polygon is the union of all its edges. -/
def boundary (poly : Polygon P n) : Set P := ⋃ i, poly.edgeSet i

/-- Definitional characterization of `edgeSet`. -/
@[simp] theorem edgeSet_eq_image_edgePath (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet i = poly.edgePath i '' Icc (0 : ℝ) 1 := rfl

end Affine

section RealModule

variable {P : Type*} {n : ℕ} [NeZero n]
variable [AddCommGroup P] [Module ℝ P]

/-- The `i`-th edge as an affine map in a real module. This is a version of `edgePath` for the
setting where the ambient space is itself a real module (e.g., `EuclideanSpace ℝ (Fin 2)`),
which is useful for segment-based reasoning about convexity and edge intersections. -/
def edgePathModule (poly : Polygon P n) (i : Fin n) : ℝ →ᵃ[ℝ] P :=
  AffineMap.lineMap (poly.vertices i) (poly.vertices (i + 1))

/-- The `i`-th edge as a segment in a real module, defined using `segment ℝ`. This is useful
for Euclidean polygons where segment-based reasoning (convexity, intersection tests) is
more natural than the general affine `edgeSet`. See `side_eq_edgeSet` for the equivalence. -/
def side (poly : Polygon P n) (i : Fin n) : Set P :=
  segment ℝ (poly.vertices i) (poly.vertices (i + 1))

/-- The side equals the affine edge set. -/
theorem side_eq_edgeSet (poly : Polygon P n) (i : Fin n) :
    poly.side i = poly.edgeSet (V := P) i := by
  simp [side, Polygon.edgeSet, Polygon.edgePath, segment_eq_image_lineMap]

/-- The side equals the image of the edge path on `[0, 1]`. -/
@[simp] theorem side_eq_image (poly : Polygon P n) (i : Fin n) :
    poly.side i = poly.edgePathModule i '' Icc (0 : ℝ) 1 := by
  simp [side, edgePathModule, segment_eq_image_lineMap]

end RealModule

end Polygon

open scoped EuclideanGeometry

namespace EuclideanPolygon

variable {n : ℕ} [NeZero n]

/-- The length of edge `i`, i.e., the distance from vertex `i` to vertex `i + 1`. -/
noncomputable def edgeLength (poly : EuclideanPolygon n) (i : Fin n) : ℝ :=
  dist (poly.vertices i) (poly.vertices (i + 1))

/-- Edge length equals the norm of the vector between vertices.
This allows compatibility with `EuclideanGeometry`. -/
theorem edgeLength_eq_norm_vsub (poly : EuclideanPolygon n) (i : Fin n) :
    poly.edgeLength i = ‖poly.vertices (i + 1) -ᵥ poly.vertices i‖ := by
  simp [edgeLength, dist_eq_norm_vsub, norm_sub_rev]

/-- The interior angle at vertex `i`, measured from vertex `i-1` through `i` to `i+1`. -/
noncomputable def interiorAngle (poly : EuclideanPolygon n) (i : Fin n) : ℝ :=
  ∠ (poly.vertices (i - 1)) (poly.vertices i) (poly.vertices (i + 1))

/-- The perimeter of a polygon is the sum of all edge lengths. -/
noncomputable def perimeter (poly : EuclideanPolygon n) : ℝ :=
  ∑ i : Fin n, poly.edgeLength i

end EuclideanPolygon

namespace EuclideanTriangle

/-- The first vertex of a Euclidean triangle. -/
abbrev A (t : EuclideanTriangle) := t.vertices 0
/-- The second vertex of a Euclidean triangle. -/
abbrev B (t : EuclideanTriangle) := t.vertices 1
/-- The third vertex of a Euclidean triangle. -/
abbrev C (t : EuclideanTriangle) := t.vertices 2

/-- Construct a Euclidean triangle from three non-collinear points. -/
def ofPoints (a b c : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![a, b, c]) :
    EuclideanTriangle :=
  { vertices := ![a, b, c]
    n_ge_3 := le_refl 3
    verticesNoncollinear := h }

/-- The first vertex of `ofPoints a b c h` is `a`. -/
@[simp] theorem ofPoints_A (a b c : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![a, b, c]) :
    (ofPoints a b c h).A = a := rfl

/-- The second vertex of `ofPoints a b c h` is `b`. -/
@[simp] theorem ofPoints_B (a b c : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![a, b, c]) :
    (ofPoints a b c h).B = b := rfl

/-- The third vertex of `ofPoints a b c h` is `c`. -/
@[simp] theorem ofPoints_C (a b c : EuclideanSpace ℝ (Fin 2)) (h : AffineIndependent ℝ ![a, b, c]) :
    (ofPoints a b c h).C = c := rfl

/-- Convert a Euclidean triangle to an `Affine.Triangle`. -/
def toAffineTriangle (t : EuclideanTriangle) : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨t.vertices, t.verticesNoncollinear⟩

/-- The vertices of the affine triangle match. -/
@[simp] theorem toAffineTriangle_points (t : EuclideanTriangle) (i : Fin 3) :
    t.toAffineTriangle.points i = t.vertices i := rfl

/-- Construct a Euclidean triangle from an `Affine.Triangle`. -/
def ofAffineTriangle (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) : EuclideanTriangle :=
  { vertices := t.points
    n_ge_3 := le_refl 3
    verticesNoncollinear := t.independent }

/-- Round-trip conversion: `Affine.Triangle` to `EuclideanTriangle` and back is the identity. -/
@[simp] theorem ofAffineTriangle_toAffineTriangle
    (t : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) :
    (ofAffineTriangle t).toAffineTriangle = t := by
  ext i
  rfl

/-- Round-trip conversion: `EuclideanTriangle` to `Affine.Triangle` and back is the identity. -/
@[simp] theorem toAffineTriangle_ofAffineTriangle (t : EuclideanTriangle) :
    ofAffineTriangle t.toAffineTriangle = t := by
  cases t
  rfl

end EuclideanTriangle
