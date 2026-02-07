/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Geometry.Polygon.Basic

/-!
# Simple Polygons
-/

@[expose] public section

variable {R V P : Type*} [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

namespace Polygon

variable {poly : Polygon P n}

variable (R) in
/-- A polygon is simple if non-adjacent edges are disjoint
and adjacent edges meet only at their shared vertex. -/
def IsSimple (poly : Polygon P n) : Prop :=
  (∀ i j : Fin n, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
    Disjoint (poly.edgeSet R i) (poly.edgeSet R j)) ∧
  (∀ i : Fin n,
    poly.edgeSet R i ∩ poly.edgeSet R (i + 1) = {poly (i + 1)})

namespace IsSimple

theorem nonadjacent_disjoint {i j : Fin n} (h : poly.IsSimple R)
    (hij : i ≠ j) (hi : i ≠ j + 1) (hj : j ≠ i + 1) :
    Disjoint (poly.edgeSet R i) (poly.edgeSet R j) :=
  h.left i j hij hi hj

theorem adjacent_inter (h : poly.IsSimple R) (i : Fin n) :
    poly.edgeSet R i ∩ poly.edgeSet R (i + 1) = {poly (i + 1)} :=
  h.right i

end IsSimple

end Polygon
