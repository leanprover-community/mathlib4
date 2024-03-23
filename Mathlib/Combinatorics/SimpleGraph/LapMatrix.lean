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
* `SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`:
  The number of connected components in `G`
  is the dimension of the nullspace of its Laplacian matrix.
-/


open BigOperators Finset Matrix

namespace SimpleGraph

variable {V : Type*} (R : Type*)
variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

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
    (G.lapMatrix R *ᵥ vec) v = G.degree v * vec v - ∑ u in G.neighborFinset v, vec u := by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]

theorem lapMatrix_mulVec_eq_zero_of_forall_adj [NonAssocRing R] {vec : V → R}
    (h : ∀ v w, G.Adj v w → vec v = vec w) : G.lapMatrix R *ᵥ vec = 0 := by
  ext1 v
  have : ∀ w ∈ G.neighborFinset v, vec w = vec v := by simpa [eq_comm] using h v
  simp [lapMatrix_mulVec_apply, sum_congr rfl this]

theorem lapMatrix_mulVec_const_eq_zero [NonAssocRing R] : mulVec (G.lapMatrix R) (fun _ ↦ 1) = 0 :=
  lapMatrix_mulVec_eq_zero_of_forall_adj _ fun _ _ _ ↦ rfl

theorem dotProduct_mulVec_degMatrix [Ring R] (x y : V → R) :
    x ⬝ᵥ (G.degMatrix R *ᵥ y) = ∑ i : V, G.degree i * x i * y i := by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, ← Nat.cast_comm]

theorem dotProduct_mulVec_lapMatrix [Ring R] (x y : V → R) :
    x ⬝ᵥ (G.lapMatrix R *ᵥ y) = ∑ e in G.edgeFinset,
      Sym2.lift ⟨fun v w ↦ (x v - x w) * (y v - y w), fun _ _ ↦ by ring⟩ e := by


variable (R)

theorem degree_eq_sum_if_adj [AddCommMonoidWithOne R] (i : V) :
    (G.degree i : R) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold degree neighborFinset neighborSet
  rw [sum_boole, Set.toFinset_setOf]

theorem lapMatrix_toLinearMap₂'_apply [CommRing R] (x y : V → R) :
    toLinearMap₂' (G.lapMatrix R) x y = ∑ e in G.edgeFinset,
      Sym2.lift ⟨fun v w ↦ (x v - x w) * (y v - y w), fun _ _ ↦ by ring⟩ e := by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix]
  simp_rw [sub_mul, mul_sub]

/-- Let $L$ be the graph Laplacian and let $x \in \mathbb{R}$, then
$$x^{\top} L x = \sum_{i \sim j} (x_{i}-x_{j})^{2}$$,
where $\sim$ denotes the adjacency relation -/
theorem lapMatrix_toLinearMap₂' [Field R] [CharZero R] (x : V → R) :
    toLinearMap₂' (G.lapMatrix R) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← half_add_self (∑ x_1 : V, ∑ x_2 : V, _)]
  conv_lhs => enter [1,2,2,i,2,j]; rw [if_congr (adj_comm G i j) rfl rfl]
  conv_lhs => enter [1,2]; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

/-- The Laplacian matrix is positive semidefinite -/
theorem posSemidef_lapMatrix [LinearOrderedField R] [StarOrderedRing R] [TrivialStar R] :
    PosSemidef (G.lapMatrix R) := by
  constructor
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · intro x
    rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity

variable {G R}

theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj [LinearOrderedField R] {x : V → R} :
    Matrix.toLinearMap₂' (G.lapMatrix R) x x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]

theorem lapMatrix_toLin'_apply_eq_zero_iff_forall_adj (x : V → ℝ) :
    Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]

theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable (x : V → ℝ) :
    Matrix.toLinearMap₂' (G.lapMatrix ℝ) x x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA ↦ h i j hA.reachable⟩
  · intro h i j ⟨w⟩
    induction' w with w i j _ hA _ h'
    · rfl
    · exact (h i j hA).trans h'

theorem lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable {x : V → ℝ} :
    Matrix.toLin' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← (posSemidef_lapMatrix ℝ G).toLinearMap₂'_zero_iff, star_trivial,
      lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

lemma comp_connectedComponentMk_mem_ker_toLin'_lapMatrix [CommRing R]
    (f : G.ConnectedComponent → R) :
    f ∘ connectedComponentMk G ∈ LinearMap.ker (toLin' (lapMatrix R G)) :=
  lapMatrix_mulVec_eq_zero_of_forall_adj _ fun _ _ h ↦ congr_arg f <|
    ConnectedComponent.eq.2 h.reachable

lemma mem_ker_toLin'_lapMatrix_of_connectedComponent [CommRing R] (c : G.ConnectedComponent) :
    Set.indicator (connectedComponentMk G ⁻¹' {c}) 1 ∈ LinearMap.ker (toLin' (lapMatrix R G)) :=
  comp_connectedComponentMk_mem_ker_toLin'_lapMatrix <| Set.indicator {c} 1

variable (G)

/-- `lapMatrix_ker_basis G` is a basis of the nullspace indexed by its connected components,
the basis is made up of the functions `V → ℝ` which are `1` on the vertices of the given
connected component and `0` elsewhere. -/
noncomputable def lapMatrix_ker_basis :
    Basis (ConnectedComponent G) ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) :=
  .ofEquivFun <| .symm
    { toFun := fun f ↦ ⟨f ∘ connectedComponentMk G,
        comp_connectedComponentMk_mem_ker_toLin'_lapMatrix f⟩,
      invFun := fun f ↦ ConnectedComponent.lift f.1 fun v w p _ ↦
        lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable.1 f.2 v w p.reachable,
      left_inv := fun _ ↦ funext <| ConnectedComponent.forall.2 fun _ ↦ rfl,
      right_inv := fun _ ↦ rfl,
      map_add' := fun _ _ ↦ rfl,
      map_smul' := fun _ _ ↦ rfl }

/-- The number of connected components in `G` is the dimension of the nullspace its Laplacian. -/
theorem card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix :
    Fintype.card G.ConnectedComponent =
      FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by
  rw [FiniteDimensional.finrank_eq_card_basis (lapMatrix_ker_basis G)]

@[deprecated] -- 2024-03-22
alias card_ConnectedComponent_eq_rank_ker_lapMatrix :=
  card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix

end SimpleGraph
