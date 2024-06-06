/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric

#align_import combinatorics.simple_graph.adj_matrix from "leanprover-community/mathlib"@"3e068ece210655b7b9a9477c3aff38a492400aa1"

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `Matrix.IsAdjMatrix`: `A : Matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `Matrix.IsAdjMatrix.to_graph`: for `A : Matrix V V α` and `h : A.IsAdjMatrix`,
  `h.to_graph` is the simple graph induced by `A`.

* `Matrix.compl`: for `A : Matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `SimpleGraph.adjMatrix`: the adjacency matrix of a `SimpleGraph`.

* `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`: each entry of the `n`th power of
  a graph's adjacency matrix counts the number of length-`n` walks between the corresponding
  pair of vertices.

-/


open Matrix

open Finset Matrix SimpleGraph

variable {V α β : Type*}

namespace Matrix

/-- `A : Matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by aesop
  symm : A.IsSymm := by aesop
  apply_diag : ∀ i, A i i = 0 := by aesop
#align matrix.is_adj_matrix Matrix.IsAdjMatrix

namespace IsAdjMatrix

variable {A : Matrix V V α}

@[simp]
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) :
    ¬A i i = 1 := by simp [h.apply_diag i]
#align matrix.is_adj_matrix.apply_diag_ne Matrix.IsAdjMatrix.apply_diag_ne

@[simp]
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]
#align matrix.is_adj_matrix.apply_ne_one_iff Matrix.IsAdjMatrix.apply_ne_one_iff

@[simp]
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]
#align matrix.is_adj_matrix.apply_ne_zero_iff Matrix.IsAdjMatrix.apply_ne_zero_iff

/-- For `A : Matrix V V α` and `h : IsAdjMatrix A`,
    `h.toGraph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj i j := A i j = 1
  symm i j hij := by simp only; rwa [h.symm.apply i j]
  loopless i := by simp [h]
#align matrix.is_adj_matrix.to_graph Matrix.IsAdjMatrix.toGraph

instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [toGraph]
  infer_instance

end IsAdjMatrix

/-- For `A : Matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adjMatrix`. -/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  fun i j => ite (i = j) 0 (ite (A i j = 0) 1 0)
#align matrix.compl Matrix.compl

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]
#align matrix.compl_apply_diag Matrix.compl_apply_diag

@[simp]
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  unfold compl
  split_ifs <;> simp
#align matrix.compl_apply Matrix.compl_apply

@[simp]
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [compl, h.apply, eq_comm]
#align matrix.is_symm_compl Matrix.isSymm_compl

@[simp]
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }
#align matrix.is_adj_matrix_compl Matrix.isAdjMatrix_compl

namespace IsAdjMatrix

variable {A}

@[simp]
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm
#align matrix.is_adj_matrix.compl Matrix.IsAdjMatrix.compl

theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  cases' h.zero_or_one v w with h h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]
#align matrix.is_adj_matrix.to_graph_compl_eq Matrix.IsAdjMatrix.toGraph_compl_eq

end IsAdjMatrix

end Compl

end Matrix

open Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (α)

/-- `adjMatrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0
#align simple_graph.adj_matrix SimpleGraph.adjMatrix

variable {α}

-- TODO: set as an equation lemma for `adjMatrix`, see mathlib4#3024
@[simp]
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl
#align simple_graph.adj_matrix_apply SimpleGraph.adjMatrix_apply

@[simp]
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [adj_comm]
#align simple_graph.transpose_adj_matrix SimpleGraph.transpose_adjMatrix

@[simp]
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G
#align simple_graph.is_symm_adj_matrix SimpleGraph.isSymm_adjMatrix

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix :=
  { zero_or_one := fun i j => by by_cases h : G.Adj i j <;> simp [h] }
#align simple_graph.is_adj_matrix_adj_matrix SimpleGraph.isAdjMatrix_adjMatrix

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not
#align simple_graph.to_graph_adj_matrix_eq SimpleGraph.toGraph_adjMatrix_eq

variable {α} [Fintype V]

@[simp]
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct (G.adjMatrix α v) vec = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]
#align simple_graph.adj_matrix_dot_product SimpleGraph.adjMatrix_dotProduct

@[simp]
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V → α) :
    dotProduct vec (G.adjMatrix α v) = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter, Finset.sum_apply]
#align simple_graph.dot_product_adj_matrix SimpleGraph.dotProduct_adjMatrix

@[simp]
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (G.adjMatrix α *ᵥ vec) v = ∑ u ∈ G.neighborFinset v, vec u := by
  rw [mulVec, adjMatrix_dotProduct]
#align simple_graph.adj_matrix_mul_vec_apply SimpleGraph.adjMatrix_mulVec_apply

@[simp]
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (vec ᵥ* G.adjMatrix α) v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v, transpose_adjMatrix]
#align simple_graph.adj_matrix_vec_mul_apply SimpleGraph.adjMatrix_vecMul_apply

@[simp]
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α * M) v w = ∑ u ∈ G.neighborFinset v, M u w := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]
#align simple_graph.adj_matrix_mul_apply SimpleGraph.adjMatrix_mul_apply

@[simp]
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M * G.adjMatrix α) v w = ∑ u ∈ G.neighborFinset w, M v u := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]
#align simple_graph.mul_adj_matrix_apply SimpleGraph.mul_adjMatrix_apply

variable (α)

@[simp]
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]
#align simple_graph.trace_adj_matrix SimpleGraph.trace_adjMatrix

variable {α}

theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α * G.adjMatrix α) i i = degree G i := by simp [filter_true_of_mem]
#align simple_graph.adj_matrix_mul_self_apply_self SimpleGraph.adjMatrix_mul_self_apply_self

variable {G}

-- @[simp] -- Porting note (#10618): simp can prove this
theorem adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} :
    (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a := by simp
#align simple_graph.adj_matrix_mul_vec_const_apply SimpleGraph.adjMatrix_mulVec_const_apply

theorem adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : ℕ} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = d * a := by
  simp [hd v]
#align simple_graph.adj_matrix_mul_vec_const_apply_of_regular SimpleGraph.adjMatrix_mulVec_const_apply_of_regular

theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction' n with n ih generalizing u v
  · obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  · simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighborFinset_def]
      apply Finset.sum_toFinset_eq_subtype
    -- Disjointness for card_bUnion
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.coeFn_mk, exists_prop] at hp;
        obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simp at hxy
#align simple_graph.adj_matrix_pow_apply_eq_card_walk SimpleGraph.adjMatrix_pow_apply_eq_card_walk

/-- The sum of the identity, the adjacency matrix, and its complement is the all-ones matrix. -/
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes [DecidableEq V] [DecidableEq α]
    [NonAssocSemiring α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = Matrix.of fun _ _ ↦ 1 := by
  ext i j
  unfold Matrix.compl
  rw [of_apply, add_apply, adjMatrix_apply, add_apply, adjMatrix_apply, one_apply]
  by_cases h : G.Adj i j
  · aesop
  · rw [if_neg h]
    by_cases heq : i = j
    · repeat rw [if_pos heq, add_zero]
    · rw [if_neg heq, if_neg heq, zero_add, zero_add, if_pos (refl 0)]

theorem dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V → α) :
    x ⬝ᵥ (G.adjMatrix α).mulVec y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0 := by
  simp only [dotProduct, mulVec, adjMatrix_apply, ite_mul, one_mul, zero_mul, mul_sum, mul_ite,
    mul_zero]

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]
variable {A : Matrix V V α} (h : IsAdjMatrix A)

/-- If `A` is qualified as an adjacency matrix,
    then the adjacency matrix of the graph induced by `A` is itself. -/
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']
#align matrix.is_adj_matrix.adj_matrix_to_graph_eq Matrix.IsAdjMatrix.adjMatrix_toGraph_eq

end Matrix.IsAdjMatrix
