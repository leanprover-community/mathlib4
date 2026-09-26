/-
Copyright (c) 2026 Rizwan Gulzar Mir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rizwan Gulzar Mir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.IncMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Oriented incidence matrix of a simple graph

This file defines the oriented (signed) incidence matrix of a finite simple graph `G`, relative
to an arbitrary linear order on the vertex set, and relates it to the graph Laplacian. This fills
part of the `TODO` in `Mathlib.Combinatorics.SimpleGraph.IncMatrix`.

## Main definitions

* `SimpleGraph.orientedIncMatrix`: `G.orientedIncMatrix R` is the oriented incidence matrix of
  `G` over the ring `R`, for an arbitrary choice of linear order on the vertex type. The
  orientation of each edge runs from its smaller-ordered endpoint to its larger-ordered one.

## Main results

* `SimpleGraph.lapMatrix_eq_orientedIncMatrix_mul_transpose`: the graph Laplacian factors as
  `B * Bᵀ`, where `B` is the oriented incidence matrix, for any choice of linear order.

## Implementation notes

Any linear order on the (possibly infinite) vertex type induces an orientation; for a finite
vertex type, `Fintype.equivFin` composed with the standard order on `Fin (card V)` gives one
canonical choice, but the results here hold for an arbitrary supplied `LinearOrder V` instance.

## TODO

* Package "an arbitrary orientation" as its own structure, not tied to a `LinearOrder V`
  instance, and show every orientation in that more general sense agrees with some
  `orientedIncMatrix` up to independently negating whichever columns/edges get the opposite
  sign convention.
-/

@[expose] public section

open Finset
open scoped Matrix

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (R : Type*) [CommRing R]

/-- The oriented (signed) incidence matrix of a finite simple graph `G`, relative to an
arbitrary linear order on the vertex type. The `(i, e)`-entry is `1` if `i` is the
smaller-ordered endpoint of the edge `e`, `-1` if `i` is the larger-ordered endpoint, and `0`
if `i` is not an endpoint of `e` or `e` is not an edge of `G`. -/
noncomputable def orientedIncMatrix [LinearOrder V] : Matrix V (Sym2 V) R :=
  .of fun i e =>
    if h : i ∈ e ∧ e ∈ G.edgeSet then
      if i < Sym2.Mem.other' h.1 then 1 else -1
    else 0

variable [LinearOrder V]

omit [Fintype V] [LinearOrder V] in
private theorem incMatrix_eq_of_mem (i : V) (e : Sym2 V) (h : i ∈ e ∧ e ∈ G.edgeSet) :
    G.incMatrix R i e = 1 :=
  G.incMatrix_of_mem_incidenceSet ⟨h.2, h.1⟩

omit [Fintype V] [LinearOrder V] in
private theorem incMatrix_eq_of_notMem (i : V) (e : Sym2 V) (h : ¬(i ∈ e ∧ e ∈ G.edgeSet)) :
    G.incMatrix R i e = 0 :=
  G.incMatrix_of_notMem_incidenceSet fun hc => h ⟨hc.2, hc.1⟩

omit [Fintype V] in
private theorem oriented_sq (i : V) (e : Sym2 V) :
    G.orientedIncMatrix R i e * G.orientedIncMatrix R i e = G.incMatrix R i e := by
  by_cases h : i ∈ e ∧ e ∈ G.edgeSet
  · rw [incMatrix_eq_of_mem G R i e h]
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_pos h]
    split_ifs <;> ring
  · rw [incMatrix_eq_of_notMem G R i e h]
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg h]
    ring

omit [Fintype V] in
private theorem oriented_mul_of_ne {i j : V} (hij : i ≠ j) (e : Sym2 V) :
    G.orientedIncMatrix R i e * G.orientedIncMatrix R j e =
      - (G.incMatrix R i e * G.incMatrix R j e) := by
  by_cases hi : i ∈ e ∧ e ∈ G.edgeSet
  · by_cases hj : j ∈ e ∧ e ∈ G.edgeSet
    · have he : e = s(i, j) := (Sym2.mem_and_mem_iff hij).mp ⟨hi.1, hj.1⟩
      subst he
      unfold orientedIncMatrix
      simp only [Matrix.of_apply]
      rw [dif_pos hi, dif_pos hj]
      have hoi : Sym2.Mem.other' hi.1 = j := by
        have hspec := Sym2.other_spec' hi.1
        rcases Sym2.eq_iff.mp hspec with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact hb
        · exact absurd ha hij
      have hoj : Sym2.Mem.other' hj.1 = i := by
        have hspec := Sym2.other_spec' hj.1
        rcases Sym2.eq_iff.mp hspec with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact absurd ha.symm hij
        · exact hb
      rw [hoi, hoj, incMatrix_eq_of_mem G R i _ hi, incMatrix_eq_of_mem G R j _ hj]
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · rw [if_pos hlt, if_neg (not_lt.mpr hlt.le)]; ring
      · rw [if_neg (not_lt.mpr hgt.le), if_pos hgt]; ring
    · rw [incMatrix_eq_of_notMem G R j e hj]
      unfold orientedIncMatrix
      simp only [Matrix.of_apply]
      rw [dif_neg hj]
      ring
  · rw [incMatrix_eq_of_notMem G R i e hi]
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg hi]
    ring

/-- **The graph Laplacian factors as `B * Bᵀ`**, where `B` is the oriented incidence matrix
of `G` relative to any linear order on the vertex type. -/
theorem lapMatrix_eq_orientedIncMatrix_mul_transpose :
    G.lapMatrix R = G.orientedIncMatrix R * (G.orientedIncMatrix R)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij
    simp_rw [oriented_sq G R i]
    have hdeg : (∑ e, G.incMatrix R i e) = (G.degree i : R) := SimpleGraph.sum_incMatrix_apply G
    rw [hdeg]
    have hadiag : (G.adjMatrix R) i i = 0 := by
      exact congrFun (G.diag_adjMatrix (α := R)) i
    rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_eq, hadiag, sub_zero]
  · simp_rw [oriented_mul_of_ne G R hij]
    rw [Finset.sum_neg_distrib]
    have hmul : (∑ e, G.incMatrix R i e * G.incMatrix R j e) =
        (G.incMatrix R * (G.incMatrix R)ᵀ) i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply]
    rw [hmul, SimpleGraph.incMatrix_mul_transpose]
    simp only [Matrix.of_apply, if_neg hij]
    rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
        Matrix.diagonal_apply_ne _ hij, zero_sub, SimpleGraph.adjMatrix_apply]

end SimpleGraph
