/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller

! This file was ported from Lean 3 source module combinatorics.simple_graph.inc_matrix
! leanprover-community/mathlib commit bb168510ef455e9280a152e7f31673cabd3d7496
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Data.Matrix.Basic

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `simple_graph.inc_matrix`: `G.inc_matrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `simple_graph.inc_matrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.inc_matrix R` and its transpose are the degrees of the vertices.
* `simple_graph.inc_matrix_mul_transpose`: Gives a complete description of the product of
  `G.inc_matrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `simple_graph.inc_matrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.inc_matrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `simple_graph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/


open Finset Matrix SimpleGraph Sym2

open BigOperators Matrix

namespace SimpleGraph

variable (R : Type _) {α : Type _} (G : SimpleGraph α)

/-- `G.inc_matrix R` is the `α × sym2 α` matrix whose `(a, e)`-entry is `1` if `e` is incident to
`a` and `0` otherwise. -/
noncomputable def incMatrix [Zero R] [One R] : Matrix α (Sym2 α) R := fun a =>
  (G.incidenceSet a).indicator 1
#align simple_graph.inc_matrix SimpleGraph.incMatrix

variable {R}

theorem incMatrix_apply [Zero R] [One R] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e :=
  rfl
#align simple_graph.inc_matrix_apply SimpleGraph.incMatrix_apply

/-- Entries of the incidence matrix can be computed given additional decidable instances. -/
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e ∈ G.incidenceSet a then 1 else 0 := by convert rfl
#align simple_graph.inc_matrix_apply' SimpleGraph.incMatrix_apply'

section MulZeroOneClass

variable [MulZeroOneClass R] {a b : α} {e : Sym2 α}

theorem incMatrix_apply_mul_incMatrix_apply :
    G.incMatrix R a e * G.incMatrix R b e = (G.incidenceSet a ∩ G.incidenceSet b).indicator 1 e :=
  by
  classical simp only [inc_matrix, Set.indicator_apply, ← ite_and_mul_zero, Pi.one_apply, mul_one,
      Set.mem_inter_iff]
#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply SimpleGraph.incMatrix_apply_mul_incMatrix_apply

theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a ≠ b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 :=
  by
  rw [inc_matrix_apply_mul_inc_matrix_apply, Set.indicator_of_not_mem]
  rw [G.incidence_set_inter_incidence_set_of_not_adj h hab]
  exact Set.not_mem_empty e
#align simple_graph.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj SimpleGraph.incMatrix_apply_mul_incMatrix_apply_of_not_adj

theorem incMatrix_of_not_mem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [inc_matrix_apply, Set.indicator_of_not_mem h]
#align simple_graph.inc_matrix_of_not_mem_incidence_set SimpleGraph.incMatrix_of_not_mem_incidenceSet

theorem incMatrix_of_mem_incidenceSet (h : e ∈ G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [inc_matrix_apply, Set.indicator_of_mem h, Pi.one_apply]
#align simple_graph.inc_matrix_of_mem_incidence_set SimpleGraph.incMatrix_of_mem_incidenceSet

variable [Nontrivial R]

theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a :=
  by
  simp only [inc_matrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]
  exact Iff.rfl
#align simple_graph.inc_matrix_apply_eq_zero_iff SimpleGraph.incMatrix_apply_eq_zero_iff

theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e ∈ G.incidenceSet a :=
  by
  convert one_ne_zero.ite_eq_left_iff
  infer_instance
#align simple_graph.inc_matrix_apply_eq_one_iff SimpleGraph.incMatrix_apply_eq_one_iff

end MulZeroOneClass

section NonAssocSemiring

variable [Fintype α] [NonAssocSemiring R] {a b : α} {e : Sym2 α}

theorem sum_incMatrix_apply [DecidableEq α] [DecidableRel G.Adj] :
    (∑ e, G.incMatrix R a e) = G.degree a := by
  simp [inc_matrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset]
#align simple_graph.sum_inc_matrix_apply SimpleGraph.sum_incMatrix_apply

theorem incMatrix_mul_transpose_diag [DecidableEq α] [DecidableRel G.Adj] :
    (G.incMatrix R ⬝ (G.incMatrix R)ᵀ) a a = G.degree a :=
  by
  rw [← sum_inc_matrix_apply]
  simp [Matrix.mul_apply, inc_matrix_apply', ← ite_and_mul_zero]
#align simple_graph.inc_matrix_mul_transpose_diag SimpleGraph.incMatrix_mul_transpose_diag

theorem sum_incMatrix_apply_of_mem_edgeSetEmbedding :
    e ∈ G.edgeSetEmbedding → (∑ a, G.incMatrix R a e) = 2 := by
  classical
    refine' e.ind _
    intro a b h
    rw [mem_edge_set] at h
    rw [← Nat.cast_two, ← card_doubleton h.ne]
    simp only [inc_matrix_apply', sum_boole, mk_mem_incidence_set_iff, h, true_and_iff]
    congr 2
    ext e
    simp only [mem_filter, mem_univ, true_and_iff, mem_insert, mem_singleton]
#align simple_graph.sum_inc_matrix_apply_of_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_mem_edgeSetEmbedding

theorem sum_incMatrix_apply_of_not_mem_edgeSetEmbedding (h : e ∉ G.edgeSetEmbedding) :
    (∑ a, G.incMatrix R a e) = 0 :=
  sum_eq_zero fun a _ => G.incMatrix_of_not_mem_incidenceSet fun he => h he.1
#align simple_graph.sum_inc_matrix_apply_of_not_mem_edge_set SimpleGraph.sum_incMatrix_apply_of_not_mem_edgeSetEmbedding

theorem incMatrix_transpose_mul_diag [DecidableRel G.Adj] :
    ((G.incMatrix R)ᵀ ⬝ G.incMatrix R) e e = if e ∈ G.edgeSetEmbedding then 2 else 0 := by
  classical
    simp only [Matrix.mul_apply, inc_matrix_apply', transpose_apply, ← ite_and_mul_zero, one_mul,
      sum_boole, and_self_iff]
    split_ifs with h
    · revert h
      refine' e.ind _
      intro v w h
      rw [← Nat.cast_two, ← card_doubleton (G.ne_of_adj h)]
      simp [mk_mem_incidence_set_iff, G.mem_edge_set.mp h]
      congr 2
      ext u
      simp
    · revert h
      refine' e.ind _
      intro v w h
      simp [mk_mem_incidence_set_iff, G.mem_edge_set.not.mp h]
#align simple_graph.inc_matrix_transpose_mul_diag SimpleGraph.incMatrix_transpose_mul_diag

end NonAssocSemiring

section Semiring

variable [Fintype (Sym2 α)] [Semiring R] {a b : α} {e : Sym2 α}

theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R ⬝ (G.incMatrix R)ᵀ) a b = (1 : R) := by
  classical
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, inc_matrix_apply_mul_inc_matrix_apply,
      Set.indicator_apply, Pi.one_apply, sum_boole]
    convert Nat.cast_one
    convert card_singleton ⟦(a, b)⟧
    rw [← coe_eq_singleton, coe_filter_univ]
    exact G.incidence_set_inter_incidence_set_of_adj h
#align simple_graph.inc_matrix_mul_transpose_apply_of_adj SimpleGraph.incMatrix_mul_transpose_apply_of_adj

theorem incMatrix_mul_transpose [Fintype α] [DecidableEq α] [DecidableRel G.Adj] :
    G.incMatrix R ⬝ (G.incMatrix R)ᵀ = fun a b =>
      if a = b then G.degree a else if G.Adj a b then 1 else 0 :=
  by
  ext (a b)
  split_ifs with h h'
  · subst b
    convert G.inc_matrix_mul_transpose_diag
  · exact G.inc_matrix_mul_transpose_apply_of_adj h'
  ·
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.inc_matrix_apply_mul_inc_matrix_apply_of_not_adj h h', sum_const_zero]
#align simple_graph.inc_matrix_mul_transpose SimpleGraph.incMatrix_mul_transpose

end Semiring

end SimpleGraph

