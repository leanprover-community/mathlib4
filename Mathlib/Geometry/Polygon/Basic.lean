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
def HasNondegenerateEdges [NeZero n] (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, poly i ≠ poly (i + 1)

theorem HasNondegenerateEdges.two_le [NeZero n] {poly : Polygon P n}
    (h : poly.HasNondegenerateEdges) : 2 ≤ n := by
  by_contra hlt
  push_neg at hlt
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  interval_cases n
  exact h 0 (by simp only [Fin.isValue, add_zero])

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [NeZero n]

variable (R) in
/-- The `i`-th edge as an affine map `R →ᵃ[R] P`. -/
def edgePath (poly : Polygon P n) (i : Fin n) : R →ᵃ[R] P :=
  AffineMap.lineMap (poly i) (poly (i + 1))

variable (R) in
/-- The `i`-th edge as a set of points using an `affineSegment`. -/
def edgeSet [PartialOrder R] (poly : Polygon P n) (i : Fin n) : Set P :=
  affineSegment R (poly i) (poly (i + 1))

variable (R) in
/-- The `edgeSet` is equivalent to the image of the `edgePath`. -/
theorem edgeSet_eq_image_edgePath [PartialOrder R] (poly : Polygon P n) (i : Fin n) :
    poly.edgeSet R i = poly.edgePath R i '' Icc (0 : R) 1 := rfl

variable (R) in
/-- The boundary of the polygon is the union of all its edges. -/
def boundary [PartialOrder R] (poly : Polygon P n) : Set P :=
  ⋃ i, poly.edgeSet R i

variable (R) in
/-- A polygon has nondegenerate vertices if any three consecutive vertices
are affinely independent. -/
def HasNondegenerateVertices (poly : Polygon P n) : Prop :=
  ∀ i : Fin n, AffineIndependent R ![poly i, poly (i + 1), poly (i + 2)]

/-- Polygons with nondegenerate vertices also have nondegenerate edges. -/
theorem HasNondegenerateVertices.hasNondegenerateEdges [Nontrivial R] {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : poly.HasNondegenerateEdges := by
  intro i
  simpa using (h i).injective.ne (by decide : (0 : Fin 3) ≠ 1)

theorem HasNondegenerateVertices.three_le [Nontrivial R] {poly : Polygon P n}
    (h : poly.HasNondegenerateVertices R) : 3 ≤ n := by
  unfold HasNondegenerateVertices at h
  specialize h 0
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, zero_add] at h
  by_contra hlt
  push_neg at hlt
  have hgt : 0 < n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  interval_cases n <;>
    exact (AffineIndependent.injective h).ne (by decide : (0 : Fin 3) ≠ 2)
      (by simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val])

end Polygon

/-! ### Interconversion with `Affine.Triangle` -/

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- Embedding from affine triangles to polygons with 3 vertices. -/
def toPolygon : Affine.Triangle R P ↪ Polygon P 3 where
  toFun t := ⟨t.points⟩
  inj' t₁ t₂ h := by
    apply Simplex.ext
    have : (⟨t₁.points⟩ : Polygon P 3).vertices =
        (⟨t₂.points⟩ : Polygon P 3).vertices := congrArg Polygon.vertices h
    intro i
    exact congrFun this i

end Affine.Triangle

namespace Polygon

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

variable (R) in
/-- Convert a polygon with 3 nondegenerate vertices to an `Affine.Triangle`. -/
def toTriangle (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R) :
    Affine.Triangle R P :=
  ⟨poly.vertices,
    by
      unfold HasNondegenerateVertices at h
      specialize h 0
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, zero_add] at h
      convert h using 1
      ext j
      fin_cases j <;> rfl⟩

/-- Converting a 3-polygon to a triangle and back yields the original polygon. -/
@[simp]
lemma toTriangle_toPolygon (poly : Polygon P 3) (h : poly.HasNondegenerateVertices R) :
    (poly.toTriangle R h).toPolygon = poly := by
  rfl

end Polygon

namespace Affine.Triangle

variable {R V P : Type*}
variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P]

/-- The polygon obtained from a triangle has nondegenerate vertices. -/
theorem toPolygon_hasNondegenerateVertices (t : Affine.Triangle R P) :
    t.toPolygon.HasNondegenerateVertices R := by
  simp only [toPolygon, Polygon.HasNondegenerateVertices, Nat.succ_eq_add_one,
    Nat.reduceAdd, Function.Embedding.coeFn_mk, Fin.isValue]
  intro i
  have h : AffineIndependent R ![t.points 0, t.points 1, t.points 2] := by
    convert t.independent using 1; funext j; fin_cases j <;> rfl
  fin_cases i <;> simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd]
  · exact h
  · exact h.comm_left.comm_right
  · exact h.comm_right.comm_left

/-- Converting a triangle to a polygon and back yields the original triangle. -/
@[simp]
lemma toPolygon_toTriangle (t : Affine.Triangle R P) :
    t.toPolygon.toTriangle R (toPolygon_hasNondegenerateVertices t) = t := by
  rfl

end Affine.Triangle
