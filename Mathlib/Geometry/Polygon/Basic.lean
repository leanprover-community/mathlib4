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
For the special case `n = 3`, an interconversion is provided with `Affine.Triangle`.

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

/-- A polygon has nondegenerate edges if adjacent vertices are distinct. -/
def NondegenerateEdges [NeZero n] (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, poly i ≠ poly (i + 1)

section Ring

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

end Ring

section DivisionRing

variable [DivisionRing R] [AddCommGroup V] [Module R V] [AddTorsor V P] [NeZero n]
variable (R)

/-- A polygon has nondegenerate vertices if no three consecutive vertices are collinear. -/
def NondegenerateVertices (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, ¬Collinear R ({poly i, poly (i + 1), poly (i + 2)} : Set P)

/-- Polygons with nondegenerate vertices also have nondegenerate edges. -/
theorem NondegenerateVertices.nondegenerateEdges {poly : Polygon P n}
    (h : poly.NondegenerateVertices R) : poly.NondegenerateEdges := by
  intro i hi
  apply h i
  rw [hi]
  convert collinear_pair R (poly (i + 1)) (poly (i + 2)) using 1
  simp only [mem_insert_iff, mem_singleton_iff, true_or, insert_eq_of_mem]

end DivisionRing

end Polygon

/-! ### Interconversion with `Affine.Triangle` -/

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Convert an affine triangle to a polygon with 3 vertices. -/
def toPolygon (t : Affine.Triangle R P) : Polygon P 3 :=
  ⟨t.points⟩

/-- The map from triangles to polygons is injective. -/
theorem toPolygon_injective : Function.Injective (toPolygon (R := R) (P := P)) := by
  intro t₁ t₂ h
  apply Simplex.ext
  have : t₁.toPolygon.vertices = t₂.toPolygon.vertices := congrArg Polygon.vertices h
  intro i
  exact congrFun this i

end Affine.Triangle

namespace Polygon

variable {R V P : Type*}
variable [DivisionRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable (R)

/-- Convert a polygon with 3 nondegenerate vertices to an `Affine.Triangle`. -/
def toTriangle (poly : Polygon P 3) (h : poly.NondegenerateVertices R) :
    Affine.Triangle R P :=
  ⟨poly.vertices, (affineIndependent_iff_not_collinear_of_ne
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
    (by decide : (1 : Fin 3) ≠ 2)).mpr (h 0)⟩

/-- Converting a 3-polygon to a triangle and back yields the original polygon. -/
@[simp]
lemma toTriangle_toPolygon (poly : Polygon P 3) (h : poly.NondegenerateVertices R) :
    (poly.toTriangle R h).toPolygon = poly := by
  rfl

end Polygon

namespace Affine.Triangle

variable {R V P : Type*}
variable [DivisionRing R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable (R)

/-- The polygon obtained from a triangle has nondegenerate vertices. -/
theorem toPolygon_nondegenerateVertices (t : Affine.Triangle R P) :
    t.toPolygon.NondegenerateVertices R := by
      simp only [toPolygon, Polygon.NondegenerateVertices]
      intro i h
      have : ¬Collinear R {t.points 0, t.points 1, t.points 2} :=
        (affineIndependent_iff_not_collinear_of_ne
        (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
        (by decide : (1 : Fin 3) ≠ 2)).mp t.independent
      apply this
      fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, zero_add] at h <;>
      convert h using 1 <;> aesop

/-- Converting a triangle to a polygon and back yields the original triangle. -/
@[simp]
lemma toPolygon_toTriangle (t : Affine.Triangle R P) :
    t.toPolygon.toTriangle R (toPolygon_nondegenerateVertices R t) = t := by
  rfl

end Affine.Triangle
