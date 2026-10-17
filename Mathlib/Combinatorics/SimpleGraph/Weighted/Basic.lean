/-
Copyright (c) 2026 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Weighted Graphs with and without Killing Term

In this file we introduce `WeightedGraph` and `WeightedGraphWithKillingTerm`. Weighted graphs
have general use in graph theory, and weighted graphs with a killing term are used in the study of
Dirichlet forms on discrete spaces.

## Main results

- `WeightedGraph`: defines a weighted graphs as a `SimpleGraph` with a non-negative real-valued
  symmetric `WeightedGraph.edgeWeight` function.
- `WeightedGraphWithKillingTerm`: extends `WeightedGraph` by adding a non-negative real-valued
  function defined on the vertices of the graph.
- `StandardWeights`: a proposition that the killing term is 0 and the edgeWeight function is induced
  by the underlying adjaceny relations such that an edge has weight 1 if it exists and 0 otherwise.

- `degree`: defines the degree of a vertex of a `WeightedGraphWithKillingTerm`.
- `degreeWithStandardWeights`: If a graph has standard weights then the degree in the sense of
  `WeightedGraphWithKillingTerm.degree` coincides with the `SimpleGraph.degree`.

- `associatedForm`: the bilinear form associated to a `WeightedGraphWithKillingTerm`
- `associatedForm_of_basis_eq_degree`: The form associated to a `WeightedGraphWithKillingTerm` is
  equal to the degree of a vertex `x`, when passed the standard basis function with support at `x`.
- `associatedForm_neq_basisFuns_eq_neq_edgeWeight`: The form associated to a
  `WeightedGraphWithKillingTerm` is equal to negative the edge weight, when passed the standard
  basis functions with support at each vertex of the edge.
- `associatedForm_at_basisVec_eq_killingTerm`: The form associated to a
  `WeightedGraphWithKillingTerm` is equal to the killing term of a vertex `x` when passed the
  standard basis function with support at `x` and the constant 1 function.

## Notation

 - `𝟙_x` : The indicator function with support at x, see `basisFun`.

## References

* [M. Keller, D. Lenz, R. K. Wojciechowski, *Graphs and Discrete Dirichlet Spaces*][keller2021]

## To-Do
- Define Dirichlet forms and graph Laplacians and prove their basic properties.

-/
@[expose] public section

open NNReal

/--
A WeightedGraph is a simple graph with a non-negative real-valued symmetric edge weight function
that is 0 if and only if two vertices are not adjacent.
-/
@[ext]
structure WeightedGraph (X : Type*) extends SimpleGraph X where
  /-- The function that takes the endpoints of an edge and returns the edge's weight -/
  edgeWeight : X → X → ℝ≥0
  /-- The edge weight function is symmetric. -/
  edgeWeight_symm : IsSymmOp edgeWeight
  /-- An edge weight is greater than 0 if and only if the corresponding vertices are adjacent. -/
  edgeDef (u v : X) : Adj u v ↔ 0 < edgeWeight u v

variable {X : Type*}

/--
Two vertices are not adjacent if and only if the weight of the edge connecting them is 0 (i.e. no
such edge exists).
-/
lemma WeightedGraph.Not_Adj_iff_edgeWeight_eq_zero {x y : X} (G : WeightedGraph X) :
    ¬ G.Adj x y ↔ G.edgeWeight x y = 0 := by
  contrapose
  rw [G.edgeDef]
  exact ⟨by grind, fun h ↦ (lt_of_le_of_ne (G.edgeWeight x y).coe_nonneg (coe_ne_zero.mpr h).symm :
    (0 : ℝ) < G.edgeWeight x y)⟩

/--
No vertex is adjacent to itself, so the edge weight of loop (edge that connects a vertex to itself)
is 0.
-/
lemma WeightedGraph.no_loop {x : X} (G : WeightedGraph X) : G.edgeWeight x x = 0 :=
  (le_of_not_gt (not_imp_not.mpr (G.edgeDef x x).mpr (G.irrefl (v := x)))).ge_iff_eq.mp
  (G.edgeWeight x x).coe_nonneg

/--
The edge weight function is symmetric, so the order of its inputs can be switched.
-/
lemma WeightedGraph.edgeWeight_symm_apply (G : WeightedGraph X) (y z : X) :
    G.edgeWeight y z = G.edgeWeight z y := G.edgeWeight_symm.symm_op y z

/--
A WeightedGraphWithKillingTerm is a weighted graph with an additional non-negative real-valued
 function defined on its vertices.
-/
@[ext]
structure WeightedGraphWithKillingTerm (X : Type*) extends WeightedGraph X where
  /-- The killing term is a non-negative real-valued function on the vertices of the graph. -/
  killingTerm : X → ℝ≥0

/-! ### Declarations about Graphs with Standard Weights -/

variable (G : WeightedGraphWithKillingTerm X)

/--
A WeightedGraphWithKillingTerm has standard weights if all edges have weight 1 (and the edgeWeight
is 0, whenever two vertices are not connected by an edge), and the killing term is 0.
-/
structure StandardWeights (G : WeightedGraphWithKillingTerm X) : Prop where
  edgeWeight_Adj_iff {x y : X} : G.Adj x y ↔ G.edgeWeight x y = 1
  edgeWeight_NotAdj_iff  {x y : X} : ¬ G.Adj x y ↔ G.edgeWeight x y = 0
  killingTerm_zero : G.killingTerm = 0

variable (x y : X)

/--
If a graph has standard weights, then an edge weight is non-0 if and only if the vertices are
adjacent.
-/
lemma standardWeights_edgeWeight_neq_zero_iff_eq_one (h : StandardWeights G) :
    G.edgeWeight x y ≠ 0 ↔ G.Adj x y := by
  contrapose
  exact h.edgeWeight_NotAdj_iff.symm

/--
If a graph has standard weights, then an edge weight is not equal to 1 if and only if the vertices
are not adjacent.
-/
lemma standardWeights_edgeWeight_neq_one_iff_eq_zero (h : StandardWeights G) :
    G.edgeWeight x y ≠ 1 ↔ ¬ G.Adj x y := by
  contrapose
  exact h.edgeWeight_Adj_iff.symm

open scoped Classical in
/--
If a graph has standard weights, then the edgeWeight function can be defined piecewise as 1 if
the input vertices are adjacent and 0 otherwise.
-/
lemma standardWeights_edgeWeight_fun (h : StandardWeights G) :
    G.edgeWeight = fun x y ↦ if G.Adj x y then 1 else 0 := by
  ext x y
  by_cases hyp : G.Adj x y <;> simp [hyp, h.edgeWeight_NotAdj_iff.mp, h.edgeWeight_Adj_iff.mp]

open scoped Classical in
/--
If a graph has standard weights, then the edgeWeight function can be defined piecewise as 0 if
the input vertices are not adjacent and 1 otherwise.
-/
lemma standardWeights_edgeWeight_fun' (h : StandardWeights G) :
    G.edgeWeight = fun x y ↦ if ¬ G.Adj x y then 0 else 1 := by
  grind [standardWeights_edgeWeight_fun]

/--
If a graph has standard weights, then an edge is in the edgeSet if and only if the associated
edge weight is 1.
-/
lemma standardWeightEdgeSet_in (h : StandardWeights G) :
    s(x, y) ∈ G.edgeSet ↔ G.edgeWeight x y = 1 := (G.mem_edgeSet).trans h.edgeWeight_Adj_iff

/--
If a graph has standard weights, then an edge is not in the edgeSet if and only if the associated
edge weight is 0.
-/
lemma standardWeightEdgeSet_notin (h : StandardWeights G) :
    s(x, y) ∉ G.edgeSet ↔ G.edgeWeight x y = 0 := by
  grind [h.edgeWeight_NotAdj_iff, G.mem_edgeSet]

variable [Fintype X]

/--
The degree of a vertex x of a WeightedGraphWithKillingTerm is non-negative and defined as
∑ y, (G.edgeWeight x y) + (G.killingTerm x).
-/
def WeightedGraphWithKillingTerm.degree (x : X) : ℝ≥0 :=
  ∑ y, (G.edgeWeight x y) + (G.killingTerm x)

open scoped Classical in
/--
If a WeightedGraphWithKillingTerm has standard weights, then its notion of degree coincides with
the notion of degree on the underlying simple graph.
-/
lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = G.toSimpleGraph.degree x := by
  simp only [WeightedGraphWithKillingTerm.degree, h.killingTerm_zero, Pi.zero_apply, add_zero,
    ← G.card_neighborFinset_eq_degree, G.neighborFinset_def, SimpleGraph.neighborSet,
    Finset.cast_card]
  rw [← Finset.sum_filter_ne_zero]
  congr! with y hy
  · grind [standardWeights_edgeWeight_neq_zero_iff_eq_one]
  exact h.edgeWeight_Adj_iff.mp ((G.toSimpleGraph.mem_neighborFinset x y).mp hy)

open scoped Classical in
lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.degree x = (G.neighborFinset x).card := by
  simp [degreeWithStandardWeights G h x]

namespace WeightedGraphWithKillingTerm

/-! ### Declarations about the Form Associated to Weighted Graphs with Killing Term -/

/--
The definition of the form associated to a `WeightedGraphWithKillingTerm`.
-/
noncomputable
def associatedFormFun (f g : X → ℝ) :=
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x

open Finset

lemma associatedFormBilinearMap :
    IsBilinearMap (R := ℝ) G.associatedFormFun where
  add_left f g h := by
    apply sub_eq_zero.mp
    simp [associatedFormFun, sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_left c f g := by
    unfold associatedFormFun
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
  add_right f g h := by
    apply sub_eq_zero.mp
    simp [associatedFormFun, sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_right c f g := by
    unfold associatedFormFun
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
    apply sub_eq_zero.mp
    ring_nf

/--
The associated form as a bilinear map.
-/
noncomputable
def associatedForm := G.associatedFormBilinearMap.toLinearMap

lemma associatedForm_apply {f g} : G.associatedForm f g =
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x := by rfl

open scoped Classical in
/-- We define the indicator functions to be our standard basis functions for X → ℝ -/
noncomputable
abbrev basisFun (y : X) : X → ℝ := Pi.single y 1

/-- We use the notation 𝟙_ to write this basis/indicator function more concisely. -/
scoped notation "𝟙_" y:max => basisFun y

lemma sum_killingTerm_weight_mul_basisFun_sq_eq_killingTerm_mul_basisFun_sq :
    ∑ i, G.killingTerm i * (𝟙_x) i ^ 2 = G.killingTerm x := by
  simp [(Fintype.sum_subset (f := fun (y : X) ↦ G.killingTerm y * (𝟙_x) y ^ 2)
      (s := {x}) (by grind)).symm]

lemma sum_edgeWeight_mul_basisFun_sq_eq_sum_edgeWeight :
    ∑ y, ↑((G.edgeWeight x y) : ℝ) * (1 - (𝟙_x) y) ^ 2 = ∑ y, ↑(G.edgeWeight x y : ℝ) := by
  have : DecidableEq X := Classical.typeDecidableEq X
  rw [sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  nth_rw 2 [sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  congr
  · ext y
    by_cases h : y = x <;> simp_all [G.no_loop]
  simp_all [G.no_loop]

/--
The form associated to a `WeightedGraphWithKillingTerm` is equal to the degree of a vertex `x`, when
passed the standard basis function with support at `x`.
-/
lemma associatedForm_of_basis_eq_degree :
    G.associatedForm (𝟙_x) (𝟙_x) = G.degree x := by
  have : DecidableEq X := Classical.typeDecidableEq X
  simp only [associatedForm_apply, degree, one_div, NNReal.coe_add, NNReal.coe_sum]
  field_simp
  rw [sum_killingTerm_weight_mul_basisFun_sq_eq_killingTerm_mul_basisFun_sq, mul_add,
    sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  congr
  simp only [Pi.single_eq_same, sum_edgeWeight_mul_basisFun_sq_eq_sum_edgeWeight, two_mul]
  congr 1
  nth_rw 2 [sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  simp only [G.no_loop, NNReal.coe_zero, add_zero]
  congr! with y h
  have : y ≠ x := by grind
  rw [sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  simp only [ne_eq, this, not_false_eq_true, Pi.single_eq_of_ne, zero_sub, even_two, Even.neg_pow,
    Pi.single_eq_same, one_pow, mul_one, G.edgeWeight_symm_apply]
  apply add_eq_right.mpr
  rw [← sum_const_zero]
  congr! with z h'
  grind

lemma neq_basis_vecs_imp_sum_weighted_killingTerm_neq_basisFun_eq_zero (x y : X) (h : x ≠ y) :
    ∑ z, G.killingTerm z * (𝟙_x) z * (𝟙_y) z = 0 := by
  have : DecidableEq X := Classical.typeDecidableEq X
  have : (𝟙_y) x = 0 := by grind
  rw [sum_eq_sum_sdiff_singleton_add (i := x) (by simp), this, mul_zero, add_zero,
    ← sum_const_zero (s := (_ : Finset X))]
  congr! with y h
  grind

/--
The form associated to a `WeightedGraphWithKillingTerm` is equal to negative the edge weight, when
passed the standard basis functions with support at each vertex of the edge.
-/
lemma associatedForm_neq_basisFuns_eq_neq_edgeWeight (x y : X) (h : x ≠ y) :
    G.associatedForm (𝟙_x) (𝟙_y) = - G.edgeWeight x y := by
  have : DecidableEq X := Classical.typeDecidableEq X
  simp only [associatedForm_apply, one_div]
  field_simp
  rw [neq_basis_vecs_imp_sum_weighted_killingTerm_neq_basisFun_eq_zero (h := h), mul_zero, add_zero,
    sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  nth_rw 2 [sum_eq_sum_sdiff_singleton_add (i := y) (by simp)]
  conv => lhs; congr; rfl; arg 2; simp [h]
  conv => lhs; congr; congr; rfl; ext z; rw [sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  rw [sum_congr (s₁ := univ \ {y}) (s₂ := univ \ {y}) (g := fun _ ↦ 0) (by simp) (by simp_all),
    sum_const_zero, zero_add, sum_add_distrib,
    sum_congr (s₂ := univ \ {x}) (g := fun _ ↦ 0)
      (by simp) (fun _ _ => by rw [sum_congr (s₁ := univ \ {x}) (s₂ := univ \ {x}) (g := fun _ ↦ 0)
      (by simp) (by simp_all), sum_const_zero]), sum_const_zero, zero_add,
    sum_eq_sum_sdiff_singleton_add (i := y) (by grind),
    sum_congr (s₂ := (univ \ {x}) \ {y}) (g := fun _ ↦ 0) (by simp) (by simp_all), sum_const_zero,
    G.edgeWeight_symm_apply]
  simp [h]
  ring

/--
The form associated to a `WeightedGraphWithKillingTerm` is equal to the killing term of a vertex `x`
when passed the standard basis function with support at x and the constant 1 function.
-/
lemma associatedForm_at_basisVec_eq_killingTerm : G.associatedForm (𝟙_x) 1 = G.killingTerm x := by
  have : DecidableEq X := Classical.typeDecidableEq X
  have : ∑ x_1 ∈ univ \ {x}, ↑(G.killingTerm x_1) * (𝟙_x) x_1 = 0 := by
    rw [← sum_const_zero]; congr! with z h2; grind
  simp [associatedForm_apply]
  grind [sum_eq_sum_sdiff_singleton_add]

lemma associatedForm_isSymm : G.associatedForm.IsSymm := by
  simp only [LinearMap.isSymm_def, associatedForm_apply, one_div, Real.ringHom_apply]
  intro f g
  congr 1 <;> grind

end WeightedGraphWithKillingTerm
