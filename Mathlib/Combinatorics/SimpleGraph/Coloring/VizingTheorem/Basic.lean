/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VizingFan
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Basic Bounds for Vizing's Theorem

This file proves the basic lower bound on the chromatic index used in Vizing's
theorem.
-/

@[expose] public section

variable (n : ℕ) [Fact (0 < n)]
variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableEq (Fin n)]
  [Nonempty (Fin n)]

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- In a proper edge coloring, two edges sharing a vertex that receive the same
    color must be the same edge. -/
lemma edge_eq_of_color_eq {V : Type*} {G : SimpleGraph V} {α : Type*}
    {c : G.lineGraph.Coloring α} {e1 e2 : G.edgeSet} (v : V)
    (h1 : v ∈ e1.val) (h2 : v ∈ e2.val) (h_col : c.toFun e1 = c.toFun e2) :
    e1 = e2 := by
      by_contra h_ne
      exact absurd h_col (c.valid ⟨h_ne, v, h1, h2⟩)

set_option linter.unusedDecidableInType false in
omit [Fact (0 < n)] in
/-- **Lower bound**: the chromatic index is at least the maximum degree.

    *Proof sketch.* The edges incident to any vertex of maximum degree form
    a clique in the line graph, so the chromatic number of the line graph
    (= chromatic index) is at least the clique number, which is at least Δ. -/
lemma maxDegree_le_chromaticIndex : vizing.chromaticIndex G ≥ G.maxDegree := by
  by_contra h_contra
  push Not at h_contra
  rw [vizing.chromaticIndex] at h_contra
  obtain ⟨v, hv_max⟩ := G.exists_maximal_degree_vertex
  let incident_edges : Set G.edgeSet := {e : G.edgeSet | v ∈ (e : Sym2 (Fin n))}
  have h_incident_clique : G.lineGraph.IsClique incident_edges :=
    fun _ he1 _ he2 hne => ⟨hne, v, he1, he2⟩
  have h_clique_size : incident_edges.ncard = G.maxDegree := by
    have h_image : Subtype.val '' incident_edges = G.incidenceSet v := by
      ext e; constructor
      · rintro ⟨⟨e', he'⟩, hv', rfl⟩; exact ⟨he', hv'⟩
      · rintro ⟨he, hv⟩; exact ⟨⟨e, he⟩, hv, rfl⟩
    have h_ncard : incident_edges.ncard = (G.incidenceSet v).ncard := by
      rw [← h_image, Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [h_ncard, hv_max, ← G.card_incidenceFinset_eq_degree v,
      ← Set.ncard_coe_finset, G.coe_incidenceFinset v]
  have h_cliqueNum : G.lineGraph.cliqueNum ≥ G.maxDegree := by
    have h_nclique : G.lineGraph.IsNClique G.maxDegree incident_edges.toFinset :=
      ⟨by rw [Set.coe_toFinset]; exact h_incident_clique,
       by rw [← Set.ncard_eq_toFinset_card']; exact h_clique_size⟩
    have h_le := h_nclique.isClique.card_le_cliqueNum
    rw [h_nclique.card_eq] at h_le; exact h_le
  have h_chi_ge : (G.lineGraph.chromaticNumber : ℕ∞) ≥ (G.maxDegree : ℕ∞) :=
    le_trans (by exact_mod_cast h_cliqueNum) G.lineGraph.cliqueNum_le_chromaticNumber
  have h_chi_ge_nat : G.lineGraph.chromaticNumber.toNat ≥ G.maxDegree := by
    cases h : G.lineGraph.chromaticNumber with
    | top =>
      exfalso
      have h_le := (SimpleGraph.colorable_of_fintype G.lineGraph).chromaticNumber_le
      rw [h, top_le_iff] at h_le
      exact ENat.natCast_ne_top _ h_le
    | coe n => rw [h] at h_chi_ge; exact_mod_cast h_chi_ge
  omega

set_option linter.style.haveILetI false in
omit [Fact (0 < n)] [DecidableEq (Fin n)] [Nonempty (Fin n)] in
/-- The empty graph has chromatic index 0. -/
lemma chromaticIndex_bot :
    let G_empty : SimpleGraph (Fin n) := ⊥
    vizing.chromaticIndex G_empty = 0 := by
  change vizing.chromaticIndex (⊥ : SimpleGraph (Fin n)) = 0
  unfold vizing.chromaticIndex
  haveI : IsEmpty ((⊥ : SimpleGraph (Fin n)).edgeSet) := by
    rw [SimpleGraph.edgeSet_bot]; infer_instance
  rw [SimpleGraph.chromaticNumber_eq_zero_of_isEmpty]; rfl

omit [Fact (0 < n)] [Nonempty (Fin n)] [DecidableEq (Fin n)] in
/-- Extend an edge coloring of `G \ {e}` to all of `G` by assigning `color`
    to `e`, given that `color` is unused at both endpoints. -/
lemma extendColoringOneEdge (e : G.edgeSet)
    {u v : Fin n} (huv : e.val = s(u, v))
    (c' : vizing.edgeColoring (G.deleteEdges {e.val}) (Fin (G.maxDegree + 1)))
    (color : Fin (G.maxDegree + 1))
    (h_free_u : ∀ e₁ : (G.deleteEdges {e.val}).edgeSet,
                  u ∈ e₁.val → c'.toFun e₁ ≠ color)
    (h_free_v : ∀ e₂ : (G.deleteEdges {e.val}).edgeSet,
                  v ∈ e₂.val → c'.toFun e₂ ≠ color) :
    ∃ c : vizing.edgeColoring G (Fin (G.maxDegree + 1)), c.toFun e = color := by
  classical
  let lift : ∀ f : G.edgeSet, f ≠ e → (G.deleteEdges {e.val}).edgeSet :=
    fun f h => ⟨f.val, by
      rw [SimpleGraph.edgeSet_deleteEdges]
      exact ⟨f.property, fun hmem => h (Subtype.ext hmem)⟩⟩
  let toFun : G.edgeSet → Fin (G.maxDegree + 1) := fun f =>
    if h : f = e then color else c'.toFun (lift f h)
  refine ⟨SimpleGraph.Coloring.mk toFun ?_, ?_⟩
  · intro f₁ f₂ h_adj
    obtain ⟨h_ne, w, hw1, hw2⟩ := h_adj
    by_cases h1 : f₁ = e
    · have h2 : f₂ ≠ e := fun heq => h_ne (h1.trans heq.symm)
      simp only [toFun, h1, dite_eq_left rfl, dite_eq_right h2]
      have hw1' : w ∈ e.val := h1 ▸ hw1
      rw [huv, Sym2.mem_iff] at hw1'
      rcases hw1' with rfl | rfl
      · exact (h_free_u (lift f₂ h2) hw2).symm
      · exact (h_free_v (lift f₂ h2) hw2).symm
    · by_cases h2 : f₂ = e
      · simp only [toFun, dite_eq_right h1, h2, dite_eq_left rfl]
        have hw2' : w ∈ e.val := h2 ▸ hw2
        rw [huv, Sym2.mem_iff] at hw2'
        rcases hw2' with rfl | rfl
        · exact h_free_u (lift f₁ h1) hw1
        · exact h_free_v (lift f₁ h1) hw1
      · simp only [toFun, dite_eq_right h1, dite_eq_right h2]
        apply c'.valid
        refine ⟨?_, w, hw1, hw2⟩
        intro h_lift_eq
        apply h_ne; apply Subtype.ext
        change (lift f₁ h1).val = (lift f₂ h2).val
        exact congrArg Subtype.val h_lift_eq
  · change toFun e = color; simp [toFun]
