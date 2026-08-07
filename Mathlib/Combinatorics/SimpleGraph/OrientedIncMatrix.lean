/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Data.Sym.Sym2.Order

/-!
# Oriented incidence matrix

This file defines the oriented incidence matrix `G.orientedIncMatrix R` of a simple graph `G`
over a linearly ordered vertex type, and proves the Gram factorization

`G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ = G.lapMatrix R`,

the standard factorization of the graph Laplacian `D - A`. This complements the unoriented
`G.incMatrix R`, whose Gram matrix is the signless Laplacian `D + A`
(`incMatrix_mul_transpose_diag` ff.): the signs are what produce the Laplacian.

## Main definitions

* `SimpleGraph.orientedIncMatrix`: the `α × Sym2 α` matrix with, in the column of an edge
  `e = s(u, w)` with `u < w`, entry `+1` at row `w` (the larger endpoint), `-1` at row `u`,
  and `0` elsewhere; columns of non-edges are zero.

## Main results

* `SimpleGraph.orientedIncMatrix_mul_transpose`: `N * Nᵀ = D - A`.

## Implementation notes

The orientation (each edge points from its smaller to its larger endpoint) is induced by the
linear order on the vertex type. Any orientation yields the same Gram matrix, since each edge
contributes `(±1)²` to a diagonal entry and `(+1) * (-1)` to an off-diagonal one.
-/

@[expose] public section

open Finset Matrix Sym2

namespace SimpleGraph

variable (R : Type*) {α : Type*} (G : SimpleGraph α)

/-- The oriented incidence matrix: for an edge `e` incident to `v`, the entry is `+1` if `v` is
the larger endpoint of `e` and `-1` if it is the smaller one; entries vanish off the incidence
set. -/
def orientedIncMatrix [Zero R] [One R] [Neg R] [LinearOrder α] [DecidableRel G.Adj] :
    Matrix α (Sym2 α) R :=
  .of fun v e => if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0

variable {R}

section Ring

variable [Ring R] [LinearOrder α] [DecidableRel G.Adj] {u v w : α} {e : Sym2 α}

theorem orientedIncMatrix_apply :
    G.orientedIncMatrix R v e
      = if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0 := rfl

theorem orientedIncMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet v) :
    G.orientedIncMatrix R v e = 0 := by
  rw [orientedIncMatrix_apply, if_neg h]

/-- On its incidence set the oriented entry squares to `1`, so the square of any entry is the
corresponding unoriented incidence entry. -/
theorem orientedIncMatrix_mul_self :
    G.orientedIncMatrix R v e * G.orientedIncMatrix R v e = G.incMatrix R v e := by
  rw [orientedIncMatrix_apply, incMatrix_apply']
  by_cases h : e ∈ G.incidenceSet v
  · rw [if_pos h, if_pos h]
    by_cases hs : v = e.sup <;> simp [hs]
  · simp [h]

/-- The two endpoints of an edge carry opposite signs: the product of the oriented entries of
`u ≠ w` at their common edge `s(u, w)` is `-1`. -/
theorem orientedIncMatrix_apply_mul_apply_of_adj (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) * G.orientedIncMatrix R w s(u, w) = -1 := by
  have hne : u ≠ w := hadj.ne
  have hu : s(u, w) ∈ G.incidenceSet u := G.mk'_mem_incidenceSet_left_iff.2 hadj
  have hw : s(u, w) ∈ G.incidenceSet w := G.mk'_mem_incidenceSet_right_iff.2 hadj
  rw [orientedIncMatrix_apply, orientedIncMatrix_apply, if_pos hu, if_pos hw, sup_mk]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs : u ⊔ w = w := sup_eq_right.2 hlt.le
    rw [if_neg (fun h => hlt.ne (h.trans hs)), if_pos hs.symm]
    simp
  · have hs : u ⊔ w = u := sup_eq_left.2 hgt.le
    rw [if_pos hs.symm, if_neg (fun h => hgt.ne (h.trans hs))]
    simp

/-- The two endpoints of an edge carry cancelling signs: the column of an edge sums to zero
over its two endpoints. -/
theorem orientedIncMatrix_apply_add_apply_of_adj (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) + G.orientedIncMatrix R w s(u, w) = 0 := by
  have hne : u ≠ w := hadj.ne
  have hu : s(u, w) ∈ G.incidenceSet u := G.mk'_mem_incidenceSet_left_iff.2 hadj
  have hw : s(u, w) ∈ G.incidenceSet w := G.mk'_mem_incidenceSet_right_iff.2 hadj
  rw [orientedIncMatrix_apply, orientedIncMatrix_apply, if_pos hu, if_pos hw, sup_mk]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs : u ⊔ w = w := sup_eq_right.2 hlt.le
    rw [if_neg (fun h => hlt.ne (h.trans hs)), if_pos hs.symm]
    simp
  · have hs : u ⊔ w = u := sup_eq_left.2 hgt.le
    rw [if_pos hs.symm, if_neg (fun h => hgt.ne (h.trans hs))]
    simp

/-- Distinct vertices see disjoint signed columns away from their common edge: the product of
oriented entries vanishes at every `e ≠ s(u, w)`. -/
theorem orientedIncMatrix_apply_mul_apply_of_ne (hne : u ≠ w) (he : e ≠ s(u, w)) :
    G.orientedIncMatrix R u e * G.orientedIncMatrix R w e = 0 := by
  by_cases hu : e ∈ G.incidenceSet u
  · by_cases hw : e ∈ G.incidenceSet w
    · exact absurd (G.incidenceSet_inter_incidenceSet_subset hne ⟨hu, hw⟩) he
    · rw [G.orientedIncMatrix_of_notMem_incidenceSet hw, mul_zero]
  · rw [G.orientedIncMatrix_of_notMem_incidenceSet hu, zero_mul]

end Ring

section Lap

variable [Ring R] [Fintype α] [LinearOrder α] [DecidableRel G.Adj]

/-- **Laplacian factorization.** The Gram matrix of the oriented incidence matrix is the graph
Laplacian: `N * Nᵀ = D - A`. (The unoriented incidence matrix gives `D + A` instead; the signs
are what make the Laplacian.) -/
theorem orientedIncMatrix_mul_transpose :
    G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ = G.lapMatrix R := by
  ext u w
  rw [mul_apply]
  simp_rw [transpose_apply]
  by_cases huw : u = w
  · subst huw
    simp_rw [G.orientedIncMatrix_mul_self]
    rw [sum_incMatrix_apply, lapMatrix, Matrix.sub_apply, degMatrix, diagonal_apply_eq,
      adjMatrix_apply, if_neg (G.irrefl), sub_zero]
  · rw [lapMatrix, Matrix.sub_apply, degMatrix, diagonal_apply_ne _ huw, adjMatrix_apply, zero_sub]
    by_cases hadj : G.Adj u w
    · rw [if_pos hadj, Finset.sum_eq_single s(u, w)
        (fun e _ he => G.orientedIncMatrix_apply_mul_apply_of_ne huw he)
        (fun he => absurd (mem_univ _) he)]
      exact G.orientedIncMatrix_apply_mul_apply_of_adj hadj
    · rw [if_neg hadj, neg_zero]
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases eq_or_ne e s(u, w) with rfl | he
      · rw [G.orientedIncMatrix_of_notMem_incidenceSet
          (fun hmem => hadj (G.mk'_mem_incidenceSet_left_iff.1 hmem)), zero_mul]
      · exact G.orientedIncMatrix_apply_mul_apply_of_ne huw he

end Lap

end SimpleGraph
