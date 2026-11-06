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
on a linearly ordered vertex type, and proves that its Gram matrix is the Laplacian:
`G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ = G.lapMatrix R`.

## Main definitions

* `SimpleGraph.orientedIncMatrix`: the `V × Sym2 V` matrix whose column at an edge `s(u, v)`
  with `u < v` has `-1` at row `u`, `+1` at row `v` and `0` elsewhere; columns of non-edges are
  zero.

## Main results

* `SimpleGraph.orientedIncMatrix_mul_transpose`: `N * Nᵀ = G.lapMatrix R`.

## Implementation notes

Each edge is oriented from its smaller to its larger endpoint. Any orientation gives the same
Gram matrix, since each edge contributes `(±1)²` to a diagonal entry and `1 * (-1)` to an
off-diagonal one.
-/

public section

open Finset Matrix Sym2

namespace SimpleGraph

variable (R : Type*) {V : Type*} (G : SimpleGraph V)

/-- The oriented incidence matrix: for an edge `e` incident to `v`, the entry is `+1` if `v` is
the larger endpoint of `e` and `-1` if it is the smaller one; entries vanish off the incidence
set. -/
def orientedIncMatrix [Zero R] [One R] [Neg R] [LinearOrder V] [DecidableRel G.Adj] :
    Matrix V (Sym2 V) R :=
  .of fun v e => if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0

variable {R}

section Basic

variable [Zero R] [One R] [Neg R] [LinearOrder V] [DecidableRel G.Adj] {u v w : V}
  {e : Sym2 V}

theorem orientedIncMatrix_apply :
    G.orientedIncMatrix R v e =
      if e ∈ G.incidenceSet v then (if v = e.sup then 1 else -1) else 0 := by
  rfl

theorem orientedIncMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet v) :
    G.orientedIncMatrix R v e = 0 := by
  rw [orientedIncMatrix_apply, ite_eq_right h]

theorem orientedIncMatrix_apply_right (hadj : G.Adj u v) (h : u ≤ v) :
    G.orientedIncMatrix R v s(u, v) = 1 := by
  rw [orientedIncMatrix_apply, ite_eq_left (G.mk'_mem_incidenceSet_right_iff.2 hadj), sup_mk,
    ite_eq_left (sup_eq_right.2 h).symm]

theorem orientedIncMatrix_apply_left (hadj : G.Adj u v) (h : u ≤ v) :
    G.orientedIncMatrix R u s(u, v) = -1 := by
  rw [orientedIncMatrix_apply, ite_eq_left (G.mk'_mem_incidenceSet_left_iff.2 hadj), sup_mk,
    sup_eq_right.2 h, ite_eq_right hadj.ne]

end Basic

section Ring

variable [Ring R] [LinearOrder V] [DecidableRel G.Adj] {u v w : V} {e : Sym2 V}

theorem orientedIncMatrix_apply_eq_zero_iff [Nontrivial R] :
    G.orientedIncMatrix R v e = 0 ↔ e ∉ G.incidenceSet v := by
  refine ⟨fun h he => ?_, G.orientedIncMatrix_of_notMem_incidenceSet⟩
  rw [orientedIncMatrix_apply, ite_eq_left he] at h
  split_ifs at h <;> simp_all

/-- The square of an entry of the oriented incidence matrix is the corresponding entry of the
unoriented incidence matrix. -/
theorem orientedIncMatrix_mul_self :
    G.orientedIncMatrix R v e * G.orientedIncMatrix R v e = G.incMatrix R v e := by
  rw [orientedIncMatrix_apply, incMatrix_apply']
  by_cases h : e ∈ G.incidenceSet v
  · rw [ite_eq_left h, ite_eq_left h]
    by_cases hs : v = e.sup <;> simp [hs]
  · simp [h]

/-- The two endpoints of an edge carry opposite signs. -/
theorem orientedIncMatrix_apply_mul_apply_of_adj (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) * G.orientedIncMatrix R w s(u, w) = -1 := by
  rcases hadj.ne.lt_or_gt with h | h
  · rw [G.orientedIncMatrix_apply_left hadj h.le, G.orientedIncMatrix_apply_right hadj h.le,
      mul_one]
  · rw [Sym2.eq_swap, G.orientedIncMatrix_apply_right hadj.symm h.le,
      G.orientedIncMatrix_apply_left hadj.symm h.le, one_mul]

/-- The column of an edge sums to zero over its two endpoints. -/
theorem orientedIncMatrix_apply_add_apply_of_adj (hadj : G.Adj u w) :
    G.orientedIncMatrix R u s(u, w) + G.orientedIncMatrix R w s(u, w) = 0 := by
  rcases hadj.ne.lt_or_gt with h | h
  · rw [G.orientedIncMatrix_apply_left hadj h.le, G.orientedIncMatrix_apply_right hadj h.le,
      neg_add_cancel]
  · rw [Sym2.eq_swap, G.orientedIncMatrix_apply_right hadj.symm h.le,
      G.orientedIncMatrix_apply_left hadj.symm h.le, add_neg_cancel]

/-- For distinct vertices `u` and `w`, the product of their entries vanishes at every
`e ≠ s(u, w)`. -/
theorem orientedIncMatrix_apply_mul_apply_of_ne (hne : u ≠ w) (he : e ≠ s(u, w)) :
    G.orientedIncMatrix R u e * G.orientedIncMatrix R w e = 0 := by
  by_cases hu : e ∈ G.incidenceSet u
  · by_cases hw : e ∈ G.incidenceSet w
    · exact absurd (G.incidenceSet_inter_incidenceSet_subset hne ⟨hu, hw⟩) he
    · rw [G.orientedIncMatrix_of_notMem_incidenceSet hw, mul_zero]
  · rw [G.orientedIncMatrix_of_notMem_incidenceSet hu, zero_mul]

end Ring

section Lap

variable [Ring R] [Fintype V] [LinearOrder V] [DecidableRel G.Adj]

/-- The Gram matrix of the oriented incidence matrix is the Laplacian. -/
theorem orientedIncMatrix_mul_transpose :
    G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ = G.lapMatrix R := by
  ext u w
  simp_rw [mul_apply, transpose_apply]
  rcases eq_or_ne u w with rfl | huw
  · simp_rw [G.orientedIncMatrix_mul_self]
    rw [sum_incMatrix_apply, lapMatrix, Matrix.sub_apply, degMatrix, diagonal_apply_eq,
      adjMatrix_apply, ite_eq_right (G.irrefl), sub_zero]
  · rw [lapMatrix, Matrix.sub_apply, degMatrix, diagonal_apply_ne _ huw, adjMatrix_apply, zero_sub]
    by_cases hadj : G.Adj u w
    · rw [ite_eq_left hadj, Finset.sum_eq_single s(u, w)
        (fun e _ he => G.orientedIncMatrix_apply_mul_apply_of_ne huw he) (absurd <| mem_univ _)]
      exact G.orientedIncMatrix_apply_mul_apply_of_adj hadj
    · rw [ite_eq_right hadj, neg_zero]
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases eq_or_ne e s(u, w) with rfl | he
      · rw [G.orientedIncMatrix_of_notMem_incidenceSet
          (fun hmem => hadj (G.mk'_mem_incidenceSet_left_iff.1 hmem)), zero_mul]
      · exact G.orientedIncMatrix_apply_mul_apply_of_ne huw he

end Lap

end SimpleGraph
