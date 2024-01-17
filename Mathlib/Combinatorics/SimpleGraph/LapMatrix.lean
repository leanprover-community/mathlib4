/-
Copyright (c) 2023 Adrian Wüthrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Wüthrich
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Laplacian Matrix

This module defines the Laplacian matrix of a graph, and proves some of its elementary properties.

## Main definitions & Results

* `SimpleGraph.degMatrix`: The degree matrix of a simple graph
* `SimpleGraph.lapMatrix`: The Laplacian matrix of a simple graph, defined as the difference
  between the degree matrix and the adjacency matrix.
* `isPosSemidef_lapMatrix`: The Laplacian matrix is positive semidefinite.
* `rank_ker_lapMatrix_eq_card_ConnectedComponent`: The number of connected components in `G` is
  the dimension of the nullspace of its Laplacian matrix.

-/


open BigOperators Finset Matrix SimpleGraph

variable {V α : Type*} (α) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The diagonal matrix consisting of the degrees of the vertices in the graph. -/
def SimpleGraph.degMatrix [AddMonoidWithOne α] : Matrix V V α := Matrix.diagonal (G.degree ·)

/-- `lapMatrix G R` is the matrix `L = D - A` where `D`is the degree
  and `A` the adjacency matrix of `G`. -/
def SimpleGraph.lapMatrix [AddGroupWithOne α] : Matrix V V α := G.degMatrix α - G.adjMatrix α

variable {α}

theorem isSymm_lapMatrix [AddGroupWithOne α] : (G.lapMatrix α).IsSymm := by
  rw [Matrix.IsSymm, lapMatrix, degMatrix, transpose_sub, diagonal_transpose, transpose_adjMatrix]

theorem lapMatrix_mulVec_const_eq_zero [Ring α] : mulVec (G.lapMatrix α) (fun _ ↦ 1) = 0 := by
  ext1 i
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, adjMatrix_mulVec_apply, degMatrix, mulVec,
    dotProduct, diagonal]
  simp

theorem dotProduct_mulVec_adjMatrix [Ring α] (x : V → α) :
    x ⬝ᵥ mulVec (G.adjMatrix α) x = ∑ i : V, ∑ j : V, if G.Adj i j then x i * x j else 0 := by
  unfold mulVec dotProduct
  simp [mul_sum]

theorem dotProduct_mulVec_degMatrix [CommRing α] (x : V → α) :
    x ⬝ᵥ mulVec (G.degMatrix α) x = ∑ i : V, G.degree i * x i * x i := by
  unfold dotProduct degMatrix
  simp only [mulVec_diagonal, ← mul_assoc, mul_comm (x _)]

variable (α)

theorem sum_adj_eq_degree [AddCommMonoidWithOne α] (i : V) :
    (G.degree i : α) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold degree neighborFinset neighborSet
  rw [sum_boole, Set.toFinset_setOf]

/-- Let $L$ be the graph Laplacian and let $x \in \mathbb{R}$, then
 $$x^{\top} L x = \sum_{i \sim j} (x_{i}-x_{j})^{2}$$
 where $\sim$ denotes the adjacency relation -/
theorem lapMatrix_toLinearMap₂' [Field α] [CharZero α] (x : V → α) :
    toLinearMap₂' (G.lapMatrix α) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  rw [toLinearMap₂'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp only [dotProduct_sub]
  rw [dotProduct_mulVec_degMatrix, dotProduct_mulVec_adjMatrix, ← sum_sub_distrib]
  simp only [sum_adj_eq_degree, sum_mul, ← sum_sub_distrib, ite_mul, one_mul,
             zero_mul, ite_sub_ite, sub_zero]
  rw [← half_add_self (∑ x_1 : V, ∑ x_2 : V, _)]
  conv_lhs => arg 1; arg 2; arg 2; intro i; arg 2; intro j; rw [if_congr (adj_comm G i j) rfl rfl]
  conv_lhs => arg 1; arg 2; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

/-- The Laplacian matrix is positive semidefinite -/
theorem isPosSemidef_lapMatrix [LinearOrderedField α] [StarOrderedRing α] [TrivialStar α] :
    PosSemidef (G.lapMatrix α) := by
  constructor
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · intro x
    rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    refine div_nonneg (sum_nonneg' fun i ↦ sum_nonneg' fun j ↦ ?_) two_pos.le
    split
    · apply sq_nonneg
    · rfl

theorem lapMatrix_toLinearMap₂'_apply'_zero_iff_adj [LinearOrderedField α] (x : V → α) :
    Matrix.toLinearMap₂' (G.lapMatrix α) x x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  constructor
  · intro h i j
    by_contra hn
    push_neg at hn
    suffices hc : toLinearMap₂' (G.lapMatrix α) x x > 0
    · exact gt_irrefl _ (h ▸ hc)
    rw [lapMatrix_toLinearMap₂']
    refine div_pos (sum_pos' (λ k _ ↦ sum_nonneg' (λ l ↦ ?_)) ?_) two_pos
    · split_ifs
      · apply sq_nonneg
      · rfl
    · refine ⟨i, mem_univ _, sum_pos' (λ k _ ↦ ?_) ⟨j, mem_univ _, ?_⟩⟩
      · split_ifs
        · apply sq_nonneg
        · rfl
      · simpa only [hn, ite_true, gt_iff_lt, sub_pos] using
          sq_pos_of_ne_zero _ (sub_ne_zero.mpr hn.2)
  · intro h
    rw [lapMatrix_toLinearMap₂', div_eq_zero_iff]
    refine Or.inl <| sum_eq_zero λ i _ ↦ (sum_eq_zero λ j _ ↦ ?_)
    simpa only [ite_eq_right_iff, zero_lt_two, pow_eq_zero_iff, sub_eq_zero] using h i j

theorem lapMatrix_toLinearMap₂'_zero_iff_adj (x : V → ℝ) :
    Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  rw [← (isPosSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff x, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_zero_iff_adj]

theorem lapMatrix_toLinearMap₂'_apply'_zero_iff_reachable (x : V → ℝ) :
    Matrix.toLinearMap₂' (G.lapMatrix ℝ) x x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [lapMatrix_toLinearMap₂'_apply'_zero_iff_adj]
  apply Iff.intro
  · intro h i j
    unfold Reachable
    rw [Nonempty.forall]
    intro w
    induction' w with w i j _ hA _ h'
    · rfl
    · exact (h i j hA).trans h'
  · exact fun h i j hA ↦ h i j (Adj.reachable hA)

theorem ker_reachable_eq (x : V → ℝ) : Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔
    ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← (isPosSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_zero_iff_reachable]

variable [DecidableEq G.ConnectedComponent]

lemma lapMatrix_ker_basis_aux_well_defined {G : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] (c : G.ConnectedComponent) :
    (fun i ↦ if connectedComponentMk G i = c then 1 else 0) ∈
      LinearMap.ker (toLin' (lapMatrix ℝ G)) := by
  rw [LinearMap.mem_ker, ker_reachable_eq]
  intro i j h
  split_ifs with h₁ h₂ h₃
  · rfl
  · rw [← ConnectedComponent.eq] at h
    exact (h₂ (h₁ ▸ h.symm)).elim
  · rw [← ConnectedComponent.eq] at h
    exact (h₁ (h₃ ▸ h)).elim
  · rfl

/-- Given a connected component `c` of a graph `G`, `lapMatrix_ker_basis_aux c` is the map
  `V → ℝ` which is `1` on the vertices in `c` and `0` elsewhere.
  The family of these maps indexed by the connected components of `G` proves to be a basis
  of the kernel of `lapMatrix G R` -/
def lapMatrix_ker_basis_aux (c : G.ConnectedComponent) :
    LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ)) :=
  ⟨fun i ↦ if G.connectedComponentMk i = c then (1 : ℝ)  else 0,
    lapMatrix_ker_basis_aux_well_defined c⟩

lemma lapMatrix_ker_basis_aux_linearIndependent :
    LinearIndependent ℝ (lapMatrix_ker_basis_aux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i ↦ g (connectedComponentMk G i)
  · simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk, AddSubmonoid.coe_finset_sum]
    conv_lhs => enter [2, c, j]; rw [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    ext i
    simp only [Finset.sum_apply, sum_ite_eq, mem_univ, ite_true]
  rw [h] at h0
  intro c
  obtain ⟨i, h'⟩ : ∃ i : V, G.connectedComponentMk i = c := Quot.exists_rep c
  exact h' ▸ congrFun h0 i

lemma lapMatrix_ker_basis_aux_spanning :
    ⊤ ≤ Submodule.span ℝ (Set.range (lapMatrix_ker_basis_aux G)) := by
  intro x _
  rw [mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← ker_reachable_eq G x, LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
    SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true]
  rfl

/-- `lapMatrix_ker_basis G` is a basis of the nullspace indexed by its connected components,
  the basis is made up of the functions `V → ℝ` which are `1` on the vertices of the given
  connected component and `0` elsewhere. -/
noncomputable def lapMatrix_ker_basis :=
    Basis.mk (lapMatrix_ker_basis_aux_linearIndependent G) (lapMatrix_ker_basis_aux_spanning G)

/-- The number of connected components in `G` is the dimension of the nullspace its Laplacian -/
theorem rank_ker_lapMatrix_eq_card_ConnectedComponent : Fintype.card G.ConnectedComponent =
    FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by
  rw [FiniteDimensional.finrank_eq_card_basis (lapMatrix_ker_basis G)]
