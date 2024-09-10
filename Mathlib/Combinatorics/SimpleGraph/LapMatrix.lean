/-
Copyright (c) 2023 Adrian Wüthrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Wüthrich
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

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


open Finset Matrix

namespace SimpleGraph

variable {V : Type*} (R : Type*)
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degree_eq_sum_if_adj {R : Type*} [AddCommMonoidWithOne R] (i : V) :
    (G.degree i : R) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold degree neighborFinset neighborSet
  rw [sum_boole, Set.toFinset_setOf]

variable [DecidableEq V]

/-- The diagonal matrix consisting of the degrees of the vertices in the graph. -/
def degMatrix [AddMonoidWithOne R] : Matrix V V R := Matrix.diagonal (G.degree ·)

/-- The *Laplacian matrix* `lapMatrix G R` of a graph `G`
is the matrix `L = D - A` where `D` is the degree and `A` the adjacency matrix of `G`. -/
def lapMatrix [AddGroupWithOne R] : Matrix V V R := G.degMatrix R - G.adjMatrix R

variable {R}

theorem isSymm_degMatrix [AddMonoidWithOne R] : (G.degMatrix R).IsSymm :=
  isSymm_diagonal _

theorem isSymm_lapMatrix [AddGroupWithOne R] : (G.lapMatrix R).IsSymm :=
  (isSymm_degMatrix _).sub (isSymm_adjMatrix _)

theorem degMatrix_mulVec_apply [NonAssocSemiring R] (v : V) (vec : V → R) :
    (G.degMatrix R *ᵥ vec) v = G.degree v * vec v := by
  rw [degMatrix, mulVec_diagonal]

theorem lapMatrix_mulVec_apply [NonAssocRing R] (v : V) (vec : V → R) :
    (G.lapMatrix R *ᵥ vec) v = G.degree v * vec v - ∑ u ∈ G.neighborFinset v, vec u := by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]

theorem lapMatrix_mulVec_const_eq_zero [Ring R] : mulVec (G.lapMatrix R) (fun _ ↦ 1) = 0 := by
  ext1 i
  rw [lapMatrix_mulVec_apply]
  simp

theorem dotProduct_mulVec_degMatrix [CommRing R] (x : V → R) :
    x ⬝ᵥ (G.degMatrix R *ᵥ x) = ∑ i : V, G.degree i * x i * x i := by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, mul_comm]

variable (R)

/-- Let $L$ be the graph Laplacian and let $x \in \mathbb{R}$, then
$$x^{\top} L x = \sum_{i \sim j} (x_{i}-x_{j})^{2}$$,
where $\sim$ denotes the adjacency relation -/
theorem lapMatrix_toLinearMap₂' [Field R] [CharZero R] (x : V → R) :
    toLinearMap₂' R (G.lapMatrix R) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← add_self_div_two (∑ x_1 : V, ∑ x_2 : V, _)]
  conv_lhs => enter [1,2,2,i,2,j]; rw [if_congr (adj_comm G i j) rfl rfl]
  conv_lhs => enter [1,2]; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

/-- The Laplacian matrix is positive semidefinite -/
theorem posSemidef_lapMatrix [LinearOrderedField R] [StarRing R]
    [TrivialStar R] : PosSemidef (G.lapMatrix R) := by
  constructor
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · intro x
    rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity

theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj [LinearOrderedField R] (x : V → R) :
    Matrix.toLinearMap₂' R (G.lapMatrix R) x x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]

theorem lapMatrix_toLin'_apply_eq_zero_iff_forall_adj (x : V → ℝ) :
    Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]

theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable (x : V → ℝ) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) x x = 0 ↔
      ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA ↦ h i j hA.reachable⟩
  intro h i j ⟨w⟩
  induction' w with w i j _ hA _ h'
  · rfl
  · exact (h i j hA).trans h'

theorem lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable (x : V → ℝ) :
    Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

section

variable [DecidableEq G.ConnectedComponent]

lemma mem_ker_toLin'_lapMatrix_of_connectedComponent {G : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] (c : G.ConnectedComponent) :
    (fun i ↦ if connectedComponentMk G i = c then 1 else 0) ∈
      LinearMap.ker (toLin' (lapMatrix ℝ G)) := by
  rw [LinearMap.mem_ker, lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable]
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
    mem_ker_toLin'_lapMatrix_of_connectedComponent c⟩

lemma linearIndependent_lapMatrix_ker_basis_aux :
    LinearIndependent ℝ (lapMatrix_ker_basis_aux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i ↦ g (connectedComponentMk G i) := by
    simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk, AddSubmonoid.coe_finset_sum]
    repeat rw [AddSubmonoid.coe_finset_sum]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ↓reduceIte]
  rw [h] at h0
  intro c
  obtain ⟨i, h'⟩ : ∃ i : V, G.connectedComponentMk i = c := Quot.exists_rep c
  exact h' ▸ congrFun h0 i

lemma top_le_span_range_lapMatrix_ker_basis_aux :
    ⊤ ≤ Submodule.span ℝ (Set.range (lapMatrix_ker_basis_aux G)) := by
  intro x _
  rw [mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable G x,
    LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux]
  rw [AddSubmonoid.coe_finset_sum]
  simp only [SetLike.mk_smul_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rfl

/-- `lapMatrix_ker_basis G` is a basis of the nullspace indexed by its connected components,
the basis is made up of the functions `V → ℝ` which are `1` on the vertices of the given
connected component and `0` elsewhere. -/
noncomputable def lapMatrix_ker_basis :=
  Basis.mk (linearIndependent_lapMatrix_ker_basis_aux G)
    (top_le_span_range_lapMatrix_ker_basis_aux G)

end

/-- The number of connected components in `G` is the dimension of the nullspace its Laplacian. -/
theorem card_ConnectedComponent_eq_rank_ker_lapMatrix : Fintype.card G.ConnectedComponent =
    FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by
  classical
  rw [FiniteDimensional.finrank_eq_card_basis (lapMatrix_ker_basis G)]

end SimpleGraph
