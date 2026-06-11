/-
Copyright (c) 2026 Gregory Wickham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Wickham
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Hom

/-!
# Weighted Graphs with and without Killing Term

In this file we introduce `foo` and `bar`,
two main concepts in the theory of xyzzyology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.
- `bar_of_foo_of_baz`: a construction of a `bar`, given a `foo` and a `baz`.
  If this doc-string is longer than one line, subsequent lines should be indented by two spaces
  (as required by markdown syntax).
- `bar_eq`    : the main classification theorem of `bar`s.

## Notation

 - `|_|` : The barrification operator, see `bar_of_foo`.

## References

See -- include link to Graphs and Discrete Dirichlet Spaces
-/
@[expose] public section
open NNReal

@[ext]
structure WeightedGraph (X : Type*) extends SimpleGraph X where
  edgeWeight : X → X → ℝ≥0
  edgeWeight_symm : IsSymmOp edgeWeight
  edgeDef (u v : X) : Adj u v ↔ 0 < edgeWeight u v -- make a lemma for the contrapositive of this

variable {X : Type*}

@[simp]
lemma WeightedGraph.no_loop {x : X} (G : WeightedGraph X) : G.edgeWeight x x = 0 :=
  (le_of_not_gt (not_imp_not.mpr (G.edgeDef x x).mpr (G.irrefl (v := x)))).ge_iff_eq.mp
  (G.edgeWeight x x).coe_nonneg

lemma WeightedGraph.edgeWeight_symm_apply (G : WeightedGraph X) (y z : X) :
    G.edgeWeight y z = G.edgeWeight z y := G.edgeWeight_symm.symm_op y z

@[ext]
structure WeightedGraphWithKillingTerm (X : Type*) extends WeightedGraph X where
  killingTerm : X → ℝ≥0

-- Define predicates to recover simple graphs and produce them
-- Do everything for WeightedGraph, then include special cases

variable (G : WeightedGraphWithKillingTerm X)

-- Maybe let this be a special corollary that uniquely includes decidability hypotheses
-- #check fun x y ↦ if G.Adj x y then 1 else 0

--instance {x y : X} : Decidable (G.Adj x y) := by infer_instance

structure StandardWeights : Prop where
  edgeWeight_Adj_iff {x y : X} : G.Adj x y ↔ G.edgeWeight x y = 1
  edgeWeight_NotAdj_iff  {x y : X} : ¬ G.Adj x y ↔ G.edgeWeight x y = 0
  killingTerm_zero : G.killingTerm = 0

variable (x y : X)

@[simp]
lemma standardWeights_edgeWeight_neq_zero_iff_eq_one (h : StandardWeights G) :
    G.edgeWeight x y ≠ 0 ↔ G.Adj x y := by
  contrapose
  exact h.edgeWeight_NotAdj_iff.symm

@[simp]
lemma standardWeights_edgeWeight_neq_one_iff_eq_zero (h : StandardWeights G) :
    G.edgeWeight x y ≠ 1 ↔ ¬ G.Adj x y := by
  contrapose
  exact h.edgeWeight_Adj_iff.symm

-- include way to produce graph with standardweights from simpleGraph

-- Example 0.2 (Graphs with standard weights)
lemma standardWeightEdgeSet_in (h : StandardWeights G) :
    s(x, y) ∈ G.edgeSet ↔ G.edgeWeight x y = 1 := (G.mem_edgeSet).trans h.edgeWeight_Adj_iff

lemma standardWeightEdgeSet_notin (h : StandardWeights G) :
    s(x, y) ∉ G.edgeSet ↔ G.edgeWeight x y = 0 := by
  grind [h.edgeWeight_NotAdj_iff, G.mem_edgeSet]

variable [Fintype X]

def WeightedGraphWithKillingTerm.degree (x : X) : ℝ≥0 :=
  ∑ y, (G.edgeWeight x y) + (G.killingTerm x)

noncomputable
instance : Fintype ↑(G.neighborSet x) := Fintype.ofFinite (G.neighborSet x)

lemma degreeWithStandardWeights (h : StandardWeights G) (x : X) :
    G.degree x = G.toSimpleGraph.degree x := by
  simp only [WeightedGraphWithKillingTerm.degree, h.killingTerm_zero, Pi.zero_apply, add_zero,
    ← G.card_neighborFinset_eq_degree, G.neighborFinset_def, SimpleGraph.neighborSet,
    Finset.cast_card]
  rw [← Finset.sum_filter_ne_zero]
  congr! with y hy
  · grind [standardWeights_edgeWeight_neq_zero_iff_eq_one]
  exact h.edgeWeight_Adj_iff.mp ((G.toSimpleGraph.mem_neighborFinset x y).mp hy)

lemma degreeWithStandardWeightsCard (h : StandardWeights G) (x : X) :
    G.degree x = (G.neighborFinset x).card := by
  rw [degreeWithStandardWeights G h x]
  simp

namespace WeightedGraphWithKillingTerm

-- Definiton 0.5
@[simp]
noncomputable
def associatedFormFun (f g : X → ℝ) :=
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x

open Finset

def associatedFormBilinearMap :
    IsBilinearMap (R := ℝ) G.associatedFormFun where
  add_left f g h := by
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
    ring_nf
    simp [sum_add_distrib]
    ring
  smul_left c f g := by
    unfold associatedFormFun
    field_simp
    ring_nf
    simp [sum_add_distrib]
    ring_nf
    simp [mul_sum]
    ring_nf
  add_right f g h := by
    apply sub_eq_zero.mp
    simp [sub_add_eq_sub_sub]
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

noncomputable
def associatedForm := G.associatedFormBilinearMap.toLinearMap

lemma associatedForm_apply {f g} : G.associatedForm f g =
  (1/2) * ∑ x, ∑ y, (G.edgeWeight x y) * (f x - f y) * (g x - g y) +
    ∑ x, (G.killingTerm x) * f x * g x := by rfl

noncomputable
instance : DecidableEq X := by exact Classical.typeDecidableEq X

noncomputable
abbrev basisFun (y : X) : X → ℝ := Pi.single y 1

scoped notation "𝟙_" y:max => basisFun y

@[simp]
lemma sum_killingTerm_weight_mul_basisFun_sq_eq_killingTerm_mul_basisFun_sq :
    ∑ i, ↑(G.killingTerm i) * (𝟙_x) i ^ 2 = ↑(G.killingTerm x) * (𝟙_x) x ^ 2 := by
  simp [(Fintype.sum_subset (f := fun (y : X) ↦ G.killingTerm y * (𝟙_x) y ^ 2)
      (s := {x}) (by grind)).symm]

@[simp]
lemma associatedForm_of_basis_eq_degree :
    G.associatedForm (𝟙_x) (𝟙_x) = G.degree x := by
  simp only [associatedForm_apply, degree, one_div, NNReal.coe_add, NNReal.coe_sum]
  field_simp
  simp only [sum_killingTerm_weight_mul_basisFun_sq_eq_killingTerm_mul_basisFun_sq,
    Pi.single_eq_same, one_pow, mul_one]
  rw [mul_add]
  congr
  rw [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  have : ∑ x_1, ↑((G.edgeWeight x x_1) : ℝ) * (1 - (𝟙_x) x_1) ^ 2
      = ∑ x_1, ↑(G.edgeWeight x x_1 : ℝ) := by
    rw [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
    nth_rw 2 [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
    congr
    · ext y
      by_cases h : y = x <;> simp_all
    simp_all
  simp only [Pi.single_eq_same, this, two_mul]
  congr 1
  nth_rw 2 [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  simp only [G.no_loop, coe_zero, add_zero]
  congr! with y h
  have : y ≠ x := by grind
  rw [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  simp only [ne_eq, this, not_false_eq_true, Pi.single_eq_of_ne, zero_sub, even_two, Even.neg_pow,
    Pi.single_eq_same, one_pow, mul_one, G.edgeWeight_symm_apply]
  apply add_eq_right.mpr
  rw [← Finset.sum_const_zero]
  congr! with z h'
  grind

@[simp]
lemma neq_basis_vecs_imp_sum_weighted_killingTerm_neq_basisFun_eq_zero (x y : X) (h : x ≠ y) :
    ∑ z, ↑(G.killingTerm z) * (𝟙_x) z * (𝟙_y) z = 0 := by
  have : (𝟙_y) x = 0 := by grind
  rw [Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp), this, mul_zero, add_zero,
    ← Finset.sum_const_zero (s := (_ : Finset X))]
  congr! with y h
  grind

@[simp]
lemma associatedForm_neq_basisFuns_eq_neq_edgeWeight (x y : X) (h : x ≠ y) :
    G.associatedForm (𝟙_x) (𝟙_y) = - G.edgeWeight x y := by
  simp only [associatedForm_apply, one_div]
  field_simp
  rw [neq_basis_vecs_imp_sum_weighted_killingTerm_neq_basisFun_eq_zero (h := h), mul_zero, add_zero,
    Finset.sum_eq_sum_sdiff_singleton_add (i := x) (by simp)]
  nth_rw 2 [Finset.sum_eq_sum_sdiff_singleton_add (i := y) (by simp)]
  have one_y_eq_0 : (𝟙_y) x = 0 := by grind
  conv => lhs; congr; rfl; arg 2; simp [h]
  have : ∑ x_1 ∈ univ \ {y}, ↑(G.edgeWeight x x_1)
      * ((𝟙_x) x - (𝟙_x) x_1) * ((𝟙_y) x - (𝟙_y) x_1) = 0 := by
    rw [← Finset.sum_const_zero]
    congr! with z h2
    grind
  rw [this, zero_add]
  have : ∑ x_1 ∈ univ \ {x}, ∑ x_2, ↑(G.edgeWeight x_1 x_2) * ((𝟙_x) x_1 - (𝟙_x) x_2) *
    ((𝟙_y) x_1 - (𝟙_y) x_2)
   = ∑ x_1 ∈ univ \ {x}, ((∑ x_2 ∈ univ \ {x},
      ↑(G.edgeWeight x_1 x_2) * ((𝟙_x) x_1 - (𝟙_x) x_2) * ((𝟙_y) x_1 - (𝟙_y) x_2)) +
      ↑(G.edgeWeight x_1 x) * ((𝟙_x) x_1 - (𝟙_x) x) * ((𝟙_y) x_1 - (𝟙_y) x)) := by
    congr with z
    simp
  rw [this, Finset.sum_add_distrib]
  have : ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, ↑(G.edgeWeight x_1 x_2) * ((𝟙_x) x_1 -
    (𝟙_x) x_2) * ((𝟙_y) x_1 - (𝟙_y) x_2)
      = 0 := by
    suffices ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, ↑(G.edgeWeight x_1 x_2) * ((𝟙_x) x_1 -
    (𝟙_x) x_2) * ((𝟙_y) x_1 - (𝟙_y) x_2) = ∑ x_1 ∈ univ \ {x}, ∑ x_2 ∈ univ \ {x}, 0 by
      simp only [Finset.sum_const_zero] at this
      exact this
    congr! with z h2
    grind
  rw [this, zero_add, Finset.sum_eq_sum_sdiff_singleton_add (i := y) (by grind)]
  have : ↑(G.edgeWeight y x) * ((𝟙_x) y - (𝟙_x) x) * ((𝟙_y) y - (𝟙_y) x)
    = - ↑(G.edgeWeight y x) := by grind
  rw [this]
  have : ∑ x_1 ∈ (univ \ {x}) \ {y}, ↑(G.edgeWeight x_1 x) * ((𝟙_x) x_1 -
      (𝟙_x) x) * ((𝟙_y) x_1 - (𝟙_y) x) = 0 := by
    suffices ∑ x_1 ∈ (univ \ {x}) \ {y}, ↑(G.edgeWeight x_1 x) * ((𝟙_x) x_1 -
      (𝟙_x) x) * ((𝟙_y) x_1 - (𝟙_y) x) = ∑ x_1 ∈ (univ \ {x}) \ {y}, 0 by
      simp only [Finset.sum_const_zero] at this
      exact this
    congr! with z h2
    grind
  rw [this, G.edgeWeight_symm_apply]
  ring

lemma associatedForm_at_basisVec_eq_killingTerm : G.associatedForm (𝟙_x) 1 = G.killingTerm x := by
  have : ∑ x_1 ∈ univ \ {x}, ↑(G.killingTerm x_1) * (𝟙_x) x_1 = 0 := by
    rw [← Finset.sum_const_zero]; congr! with z h2; grind
  simp [associatedForm_apply]
  grind [Finset.sum_eq_sum_sdiff_singleton_add]

lemma associatedForm_isSymm : G.associatedForm.IsSymm := by
  simp only [LinearMap.isSymm_def, associatedForm_apply, one_div, Real.ringHom_apply]
  intro f g
  congr 1 <;> grind

end WeightedGraphWithKillingTerm
