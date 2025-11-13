/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Matrix.Mul

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `SimpleGraph.incMatrix`: `G.incMatrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `SimpleGraph.incMatrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.incMatrix R` and its transpose are the degrees of the vertices.
* `SimpleGraph.incMatrix_mul_transpose`: Gives a complete description of the product of
  `G.incMatrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `SimpleGraph.incMatrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.incMatrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `Sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `SimpleGraph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/

assert_not_exists Field

open Finset Matrix SimpleGraph Sym2

namespace SimpleGraph

variable (R : Type*) {α : Type*} (G : SimpleGraph α)

/-- `G.incMatrix R` is the `α × Sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
def incMatrix [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] : Matrix α (Sym2 α) R :=
  .of fun a e =>
    if e ∈ G.incidenceSet a then 1 else 0

variable {R}

theorem incMatrix_apply [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e := by
  simp [incMatrix, Set.indicator]

/-- Entries of the incidence matrix can be computed given additional decidable instances. -/
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e ∈ G.incidenceSet a then 1 else 0 := rfl

section MulZeroOneClass

variable [MulZeroOneClass R] [DecidableEq α] [DecidableRel G.Adj] {a b : α} {e : Sym2 α}

theorem incMatrix_apply_mul_incMatrix_apply : G.incMatrix R a e * G.incMatrix R b e =
    (G.incidenceSet a ∩ G.incidenceSet b).indicator 1 e := by
  simp [incMatrix_apply', Set.indicator_apply, ← ite_and, and_comm]

theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 := by
  rw [incMatrix_apply_mul_incMatrix_apply, Set.indicator_of_notMem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.notMem_empty e

theorem incMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [incMatrix_apply, Set.indicator_of_notMem h]

@[deprecated (since := "2025-05-23")]
alias incMatrix_of_not_mem_incidenceSet := incMatrix_of_notMem_incidenceSet

theorem incMatrix_of_mem_incidenceSet (h : e ∈ G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [incMatrix_apply, Set.indicator_of_mem h, Pi.one_apply]

variable [Nontrivial R]

theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a := by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]

theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e ∈ G.incidenceSet a := by
  convert one_ne_zero.ite_eq_left_iff
  infer_instance

end MulZeroOneClass

section NonAssocSemiring

variable [NonAssocSemiring R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α}

theorem sum_incMatrix_apply [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    ∑ e, G.incMatrix R a e = G.degree a := by
  simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset]

theorem incMatrix_mul_transpose_diag [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a a = G.degree a := by
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]

theorem sum_incMatrix_apply_of_mem_edgeSet [Fintype α] :
    e ∈ G.edgeSet → ∑ a, G.incMatrix R a e = 2 := by
  refine e.ind ?_
  intro a b h
  rw [mem_edgeSet] at h
  rw [← Nat.cast_two, ← card_pair h.ne]
  simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
  congr 2
  ext e
  simp

theorem sum_incMatrix_apply_of_notMem_edgeSet [Fintype α] (h : e ∉ G.edgeSet) :
    ∑ a, G.incMatrix R a e = 0 :=
  sum_eq_zero fun _ _ => G.incMatrix_of_notMem_incidenceSet fun he => h he.1

@[deprecated (since := "2025-05-23")]
alias sum_incMatrix_apply_of_not_mem_edgeSet := sum_incMatrix_apply_of_notMem_edgeSet

theorem incMatrix_transpose_mul_diag [Fintype α] [Decidable (e ∈ G.edgeSet)] :
    ((G.incMatrix R)ᵀ * G.incMatrix R) e e = if e ∈ G.edgeSet then 2 else 0 := by
  simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
    sum_boole, and_self_iff]
  split_ifs with h
  · revert h
    refine e.ind ?_
    intro v w h
    rw [← Nat.cast_two, ← card_pair (G.ne_of_adj h)]
    simp only [mk'_mem_incidenceSet_iff, G.mem_edgeSet.mp h, true_and]
    congr 2
    ext u
    simp
  · revert h
    refine e.ind ?_
    intro v w h
    simp [mk'_mem_incidenceSet_iff, G.mem_edgeSet.not.mp h]

end NonAssocSemiring

section Semiring

variable [Fintype (Sym2 α)] [DecidableEq α] [DecidableRel G.Adj] [Semiring R] {a b : α}

theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a b = (1 : R) := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
    Set.indicator_apply, Pi.one_apply, sum_boole]
  convert @Nat.cast_one R _
  convert card_singleton s(a, b)
  rw [← coe_eq_singleton, coe_filter_univ]
  exact G.incidenceSet_inter_incidenceSet_of_adj h

theorem incMatrix_mul_transpose [∀ a, Fintype (neighborSet G a)] :
    G.incMatrix R * (G.incMatrix R)ᵀ =
      of fun a b => if a = b then (G.degree a : R) else if G.Adj a b then 1 else 0 := by
  ext a b
  dsimp
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]

end Semiring

end SimpleGraph
