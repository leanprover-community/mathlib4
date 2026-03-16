/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

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

@[expose] public section


open Matrix

open Finset SimpleGraph

variable {α V : Type*}

namespace Matrix

/-- `A : Matrix V V α` is qualified as an "adjacency matrix" if
(1) every entry of `A` is `0` or `1`,
(2) `A` is symmetric,
(3) every diagonal entry of `A` is `0`. -/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by aesop
  symm : A.IsSymm := by aesop
  apply_diag : ∀ i, A i i = 0 := by aesop

namespace IsAdjMatrix

variable {A : Matrix V V α}

@[simp] protected theorem zero [Zero α] [One α] : (0 : Matrix V V α).IsAdjMatrix where

@[simp]
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) :
    ¬A i i = 1 := by simp [h.apply_diag i]

@[simp]
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]

/-- For `A : Matrix V V α` and `h : IsAdjMatrix A`,
`h.toGraph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj i j := A i j = 1
  symm i j hij := by simp only; rwa [h.symm.apply i j]
  loopless := ⟨fun i ↦ by simp [h]⟩

instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [toGraph]
  infer_instance

@[simp] theorem hadamard_self [MulZeroOneClass α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A ⊙ A = A := by ext i j; have := hA.zero_or_one i j; aesop

end IsAdjMatrix

theorem isAdjMatrix_iff_hadamard [DecidableEq V] [MonoidWithZero α]
    [IsLeftCancelMulZero α] {A : Matrix V V α} :
    A.IsAdjMatrix ↔ (A ⊙ A = A ∧ A.IsSymm ∧ 1 ⊙ A = 0) := by
  simp only [hadamard_self_eq_self_iff, IsIdempotentElem.iff_eq_zero_or_one,
    one_hadamard_eq_zero_iff, funext_iff, diag, Pi.zero_apply]
  grind [IsAdjMatrix]

/-- For `A : Matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
the complement graph of the graph induced by `A.adjMatrix`. -/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  of fun i j ↦ if i = j then 0 else if A i j = 0 then 1 else 0

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]

@[simp]
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  grind [compl, of]

@[simp]
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [compl, h.apply, eq_comm]

@[simp]
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }

theorem IsAdjMatrix.compl_inj [Zero α] [One α] {A B : Matrix V V α}
    (hA : A.IsAdjMatrix) (hB : B.IsAdjMatrix) : A.compl = B.compl ↔ A = B :=
  ⟨fun h ↦ ext fun i j ↦ by grind [of, congr($h i j), compl, IsAdjMatrix], fun h ↦ h ▸ rfl⟩

@[simp] theorem IsAdjMatrix.compl_compl [Zero α] [One α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A.compl.compl = A := by ext; grind [of, compl, IsAdjMatrix]

namespace IsAdjMatrix

variable {A}

@[simp]
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm

theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  rcases h.zero_or_one v w with h | h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]

end IsAdjMatrix

end Compl

end Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (α) in
/-- `adjMatrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0

-- TODO: set as an equation lemma for `adjMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl

@[simp]
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [adj_comm]

@[simp]
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G

variable (α)

@[simp] theorem diag_adjMatrix [Zero α] [One α] : (G.adjMatrix α).diag = 0 := by ext; simp

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by grind [adjMatrix_apply]

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not

theorem compl_adjMatrix_eq_adjMatrix_compl [DecidableEq V] [DecidableEq α] [Zero α] [One α] :
    (G.adjMatrix α).compl = Gᶜ.adjMatrix α := by aesop (add simp [Matrix.compl])

variable {G} in
theorem IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V] [AddZeroClass α]
    [One α] {H : SimpleGraph V} [DecidableRel H.Adj] (h : IsCompl G H) :
    G.adjMatrix α + H.adjMatrix α = (completeGraph V).adjMatrix α := calc
  _ = G.adjMatrix α + Gᶜ.adjMatrix α := by have := h.compl_eq; subst this; congr
  _ = _ := by aesop (add simp Matrix.compl)

@[simp] theorem adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V]
    [DecidableEq α] [AddZeroClass α] [One α] :
    G.adjMatrix α + (G.adjMatrix α).compl = (completeGraph V).adjMatrix α :=
  G.compl_adjMatrix_eq_adjMatrix_compl α ▸
    isCompl_compl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph α

/-- The sum of the identity, the adjacency matrix, and its complement is the all-ones matrix. -/
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_of_one [DecidableEq V] [DecidableEq α]
    [AddMonoid α] [One α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = of 1 := by
  aesop (add simp [add_assoc])

@[deprecated (since := "2026-01-30")] alias one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes :=
  one_add_adjMatrix_add_compl_adjMatrix_eq_of_one

variable (V)

@[simp] theorem compl_adjMatrix_completeGraph [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    ((completeGraph V).adjMatrix α).compl = 0 := by aesop (add simp Matrix.compl)

@[simp] theorem _root_.Matrix.compl_zero [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    (0 : Matrix V V α).compl = (completeGraph V).adjMatrix α := by simp [← IsAdjMatrix.compl_inj]

theorem adjMatrix_completeGraph_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V] :
    (completeGraph V).adjMatrix α = of 1 - 1 := by ext; simp [one_apply, sub_ite]

theorem _root_.Matrix.compl_zero_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (0 : Matrix V V α).compl = of 1 - 1 := by
  simp [adjMatrix_completeGraph_eq_of_one_sub_one]

@[simp] theorem _root_.Matrix.compl_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (of 1 - 1 : Matrix V V α).compl = 0 := by
  simp [← adjMatrix_completeGraph_eq_of_one_sub_one]

variable {V}

theorem adjMatrix_hadamard_self [MulZeroOneClass α] :
    G.adjMatrix α ⊙ G.adjMatrix α = G.adjMatrix α := by simp

variable {α}

section fintype
variable [Fintype V]

@[simp]
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V → α) :
    G.adjMatrix α v ⬝ᵥ vec = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V → α) :
    vec ⬝ᵥ G.adjMatrix α v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (G.adjMatrix α *ᵥ vec) v = ∑ u ∈ G.neighborFinset v, vec u := by
  rw [mulVec, adjMatrix_dotProduct]

@[simp]
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V → α) :
    (vec ᵥ* G.adjMatrix α) v = ∑ u ∈ G.neighborFinset v, vec u := by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v, transpose_adjMatrix]

@[simp]
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α * M) v w = ∑ u ∈ G.neighborFinset v, M u w := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]

@[simp]
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M * G.adjMatrix α) v w = ∑ u ∈ G.neighborFinset w, M v u := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]

variable (α) in
@[simp]
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]

theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α * G.adjMatrix α) i i = degree G i := by simp [filter_true_of_mem]

variable (R) in
/-- The number of all darts in a simple finite graph is equal to the dot product of
`G.adjMatrix α *ᵥ 1` and `1`. -/
theorem natCast_card_dart_eq_dotProduct [NonAssocSemiring α] :
    (Fintype.card G.Dart : α) = adjMatrix α G *ᵥ 1 ⬝ᵥ 1 := by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

variable {G}

theorem adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} :
    (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a := by simp

theorem adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : ℕ} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = d * a := by
  simp [hd v]

theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction n generalizing u v with
  | zero => obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  | succ n ih =>
    simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighborFinset_def]
      apply Finset.sum_toFinset_eq_subtype
    -- Disjointness for card_bUnion
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [Function.onFun, disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map, Function.Embedding.coeFn_mk] at hp
      obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simp at hxy

theorem dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V → α) :
    x ⬝ᵥ G.adjMatrix α *ᵥ y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0 := by
  simp [dotProduct, mulVec, mul_sum]

end fintype

section hadamard
variable (α) [DecidableEq V] [MulZeroOneClass α]

open Matrix

@[simp] theorem adjMatrix_hadamard_diagonal (d : V → α) :
    G.adjMatrix α ⊙ diagonal d = 0 := by simp [hadamard_diagonal]

@[simp] theorem diagonal_hadamard_adjMatrix (d : V → α) :
    diagonal d ⊙ G.adjMatrix α = 0 := by simp [diagonal_hadamard]

@[simp] theorem adjMatrix_hadamard_natCast [NatCast α] (a : ℕ) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _

@[simp] theorem natCast_hadamard_adjMatrix [NatCast α] (a : ℕ) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

@[simp] theorem adjMatrix_hadamard_ofNat [NatCast α] (a : ℕ) [a.AtLeastTwo] :
    G.adjMatrix α ⊙ ofNat(a) = 0 := adjMatrix_hadamard_diagonal _ _ _

@[simp] theorem ofNat_hadamard_adjMatrix [NatCast α] (a : ℕ) [a.AtLeastTwo] :
    ofNat(a) ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

@[simp] theorem adjMatrix_hadamard_intCast [IntCast α] (a : ℤ) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _

@[simp] theorem intCast_hadamard_adjMatrix [IntCast α] (a : ℤ) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

@[simp] theorem adjMatrix_hadamard_one :
    G.adjMatrix α ⊙ 1 = 0 := adjMatrix_hadamard_diagonal _ _ _

@[simp] theorem one_hadamard_adjMatrix :
    1 ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

end hadamard

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]
variable {A : Matrix V V α} (h : IsAdjMatrix A)

/-- If `A` is qualified as an adjacency matrix,
then the adjacency matrix of the graph induced by `A` is itself. -/
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']

end Matrix.IsAdjMatrix
