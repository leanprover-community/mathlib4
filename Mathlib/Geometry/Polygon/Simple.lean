/-
Copyright (c) 2026 A. M. Berns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. M. Berns
-/
module

public import Mathlib.Geometry.Polygon.Basic

/-!
# Simple Polygons

This file defines simple polygons based on a property characterizing a non-self-intersecting
boundary. This property is equivalent to the existence of an injective map from `AddCircle n`
to the boundary, see `Polygon.isSimple_iff_boundaryMap_injective`.
-/

@[expose] public section

variable {R V P : Type*} [Ring R] [PartialOrder R] [AddCommGroup V] [Module R V] [AddTorsor V P]
variable {n : ℕ} [NeZero n]

namespace Polygon

variable {poly : Polygon P n}

variable (R) in
/-- A polygon is simple if edges are nondegenerate, non-adjacent edges are disjoint,
and adjacent edges meet only at their shared vertex. -/
structure IsSimple (poly : Polygon P n) : Prop where
  hasNondegenerateEdges : poly.HasNondegenerateEdges
  nonadjacent_disjoint : ∀ i j : Fin n, i ≠ j → i ≠ j + 1 → j ≠ i + 1 →
    Disjoint (poly.edgeSet R i) (poly.edgeSet R j)
  adjacent_inter : ∀ i : Fin n,
    poly.edgeSet R i ∩ poly.edgeSet R (i + 1) = {poly (i + 1)}

end Polygon
