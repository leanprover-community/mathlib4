/-
Copyright (c) 2025 Kaan Tahti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kaan Tahti
-/
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Boundary of simplicial complexes

This file defines the boundary of a simplicial complex restricted to a coordinate hyperplane.

## Main definitions

* `SimplicialComplex.boundary`: The boundary of a simplicial complex on the k-th coordinate hyperplane

## Implementation notes

For a simplicial complex `S` on `Fin (n + 1) → ℝ`, the boundary `S.boundary k` is the
induced complex on the hyperplane `{x | x k = 0}`, viewed as a complex on `Fin n → ℝ`.

-/

open Set Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Geometry.SimplicialComplex

/-- The boundary of a simplicial complex on a coordinate hyperplane.
For a complex on `Fin (m + 1) → ℝ`, the boundary removes the k-th coordinate
and restricts to faces lying in the hyperplane `x_k = 0`. -/
def boundary (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1)) :
    SimplicialComplex ℝ (Fin m → ℝ) where
  faces := sorry -- The faces lying on {x | x k = 0}, with k-th coordinate removed
  empty_notMem := sorry
  indep := sorry
  down_closed := sorry
  inter_subset_convexHull := sorry

/-- Vertices of the boundary are vertices of the original complex. -/
theorem boundary_vertices_subset (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1)) :
    (S.boundary k).vertices ⊆ sorry := sorry

/-- A vertex on the boundary satisfies the coordinate constraint. -/
theorem boundary_vertex_coord (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1))
    {x : Fin m → ℝ} (hx : x ∈ (S.boundary k).vertices) :
    sorry := sorry

end Geometry.SimplicialComplex
