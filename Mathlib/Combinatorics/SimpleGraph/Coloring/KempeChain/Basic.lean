/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeColoring
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card

/-!
# Basic Kempe Chain Infrastructure

This file defines local color sets for edge colorings and the two-color Kempe
subgraph used in Vizing's theorem.
-/

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

/-! ### Coloring Observables -/

/-- Edges of `G` incident to `v`, as vertices of `G.lineGraph`. -/
def incidentEdges (G : SimpleGraph V) (v : V) : Set G.edgeSet :=
  {e : G.edgeSet | v ∈ e.val}

/-- Colors used by edges incident to `v`. -/
def incidentColors (c : G.lineGraph.Coloring α) (v : V) : Set α :=
  c.toFun '' incidentEdges G v

/-- Colors not appearing on any edge incident to `v`. -/
def missingColors (c : G.lineGraph.Coloring α) (v : V) : Set α :=
  (incidentColors c v)ᶜ

/-- `Subtype.val` maps `incidentEdges G v` onto `G.incidenceSet v`. -/
lemma incidentEdges_image_val (v : V) :
    Subtype.val '' incidentEdges G v = G.incidenceSet v := by
  ext e
  constructor
  · rintro ⟨⟨e', he'⟩, hv', rfl⟩
    exact ⟨he', hv'⟩
  · rintro ⟨he, hv⟩
    exact ⟨⟨e, he⟩, hv, rfl⟩

set_option linter.unusedDecidableInType false in

/-- The number of edges incident to `v` equals `G.degree v`. -/
lemma incidentEdges_ncard_eq_degree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    (incidentEdges G v).ncard = G.degree v := by
  have h_ncard :
      (incidentEdges G v).ncard = (G.incidenceSet v).ncard := by
    rw [← incidentEdges_image_val, Set.ncard_image_of_injective _ Subtype.val_injective]
  rw [h_ncard, ← Nat.card_coe_set_eq,
      @Nat.card_eq_fintype_card _ (SimpleGraph.incidenceSetFintype G v)]
  exact G.card_incidenceSet_eq_degree v

set_option linter.unusedDecidableInType false in
/-- The number of colors used at `v` is at most `G.degree v`. -/
lemma incidentColors_ncard_le_degree
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.lineGraph.Coloring α) (v : V) :
    (incidentColors c v).ncard ≤ G.degree v := by
  have h_finite : (incidentEdges G v).Finite := Set.toFinite _
  unfold incidentColors
  exact (Set.ncard_image_le h_finite).trans (incidentEdges_ncard_eq_degree v).le

/-- With strictly more colors than `G.degree v`, some color is missing at `v`. -/
lemma missingColors_nonempty_of_degree_lt
    [Fintype α] [Fintype V] [DecidableRel G.Adj]
    (c : G.lineGraph.Coloring α) (v : V) (h : G.degree v < Fintype.card α) :
    (missingColors c v).Nonempty := by
  classical
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have h_univ : incidentColors c v = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro col
    by_contra hcol
    exact (Set.notMem_empty col) (hempty ▸ hcol)
  have h_card : (incidentColors c v).ncard = Fintype.card α := by
    rw [h_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
  have := incidentColors_ncard_le_degree c v
  omega

/-! ### The αβ-Kempe Subgraph -/

/-- The subgraph of `G` consisting of edges colored `a` or `b` under `c`.
    Every vertex has degree at most 2 in this subgraph, since a proper coloring
    uses each color at most once per vertex. -/
def kempeSubgraph (c : G.lineGraph.Coloring α) (a b : α) : SimpleGraph V where
  Adj v w := ∃ e : G.edgeSet, e.val = s(v, w) ∧ (c.toFun e = a ∨ c.toFun e = b)
  symm.symm := by
    rintro v w ⟨e, he_val, h_col⟩
    refine ⟨e, ?_, h_col⟩
    rw [he_val, Sym2.eq_swap]
  loopless := ⟨fun v hadj => by
    obtain ⟨e, he_val, _⟩ := hadj
    exact G.irrefl (G.mem_edgeSet.mp (he_val ▸ e.property))⟩

/-- The αβ-Kempe subgraph is a subgraph of `G`. -/
lemma kempeSubgraph_le (c : G.lineGraph.Coloring α) (a b : α) :
    kempeSubgraph c a b ≤ G := by
  rintro v w ⟨e, he_val, _⟩
  exact G.mem_edgeSet.mp (he_val ▸ e.property)

/-- In a proper edge coloring, at most one edge incident to `v` receives any
    given color `col`. -/
lemma neighborSet_color_subsingleton
    (c : G.lineGraph.Coloring α) (v : V) (col : α) :
    {w : V | ∃ e : G.edgeSet, e.val = s(v, w) ∧ c.toFun e = col}.Subsingleton := by
  intro w₁ hw₁ w₂ hw₂
  obtain ⟨e₁, he₁_val, he₁_col⟩ := hw₁
  obtain ⟨e₂, he₂_val, he₂_col⟩ := hw₂
  have hv1 : v ∈ e₁.val := by rw [he₁_val]; exact Sym2.mem_mk_left v w₁
  have hv2 : v ∈ e₂.val := by rw [he₂_val]; exact Sym2.mem_mk_left v w₂
  have he_eq : e₁ = e₂ := by
    by_contra h_ne
    have h_adj : G.lineGraph.Adj e₁ e₂ := ⟨h_ne, v, hv1, hv2⟩
    have hne_col : c.toFun e₁ ≠ c.toFun e₂ := c.valid h_adj
    rw [he₁_col, he₂_col] at hne_col
    exact hne_col rfl
  have hsym_eq : s(v, w₁) = s(v, w₂) := by
    rw [← he₁_val, he_eq, he₂_val]
  rcases (Sym2.eq_iff).mp hsym_eq with ⟨_, hw⟩ | ⟨_, hw₁_eq_v⟩
  · exact hw
  · exfalso
    have hv_eq_w₁ : v = w₁ := hw₁_eq_v.symm
    rw [← hv_eq_w₁] at he₁_val
    exact G.irrefl (G.mem_edgeSet.mp (he₁_val ▸ e₁.property))

private lemma subsingleton_ncard_le_one {β : Type*} {s : Set β}
    (hs : s.Subsingleton) : s.ncard ≤ 1 := by
  by_cases h : s.Nonempty
  · obtain ⟨w, hw⟩ := h
    have hsing : s = {w} := by
      ext y; exact ⟨fun hy => hs hy hw, fun hy => hy ▸ hw⟩
    rw [hsing]; simp
  · rw [Set.not_nonempty_iff_eq_empty.mp h]; simp

/-- Every vertex has at most two neighbors in the αβ-Kempe subgraph, since
    at most one `a`-edge and one `b`-edge can be incident to it. -/
lemma kempeSubgraph_neighborSet_ncard_le_two
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) :
    ((kempeSubgraph c a b).neighborSet v).ncard ≤ 2 := by
  set N_a : Set V := {w | ∃ e : G.edgeSet, e.val = s(v, w) ∧ c.toFun e = a} with hN_a_def
  set N_b : Set V := {w | ∃ e : G.edgeSet, e.val = s(v, w) ∧ c.toFun e = b} with hN_b_def
  have h_sub : (kempeSubgraph c a b).neighborSet v ⊆ N_a ∪ N_b := by
    intro w hw
    obtain ⟨e, he_val, he_col⟩ := hw
    rcases he_col with h | h
    · exact Or.inl ⟨e, he_val, h⟩
    · exact Or.inr ⟨e, he_val, h⟩
  have hNa_sub : N_a.Subsingleton := neighborSet_color_subsingleton c v a
  have hNb_sub : N_b.Subsingleton := neighborSet_color_subsingleton c v b
  calc ((kempeSubgraph c a b).neighborSet v).ncard
      ≤ (N_a ∪ N_b).ncard := Set.ncard_le_ncard h_sub (hNa_sub.finite.union hNb_sub.finite)
    _ ≤ N_a.ncard + N_b.ncard := Set.ncard_union_le _ _
    _ ≤ 1 + 1 := add_le_add (subsingleton_ncard_le_one hNa_sub) (subsingleton_ncard_le_one hNb_sub)
    _ = 2 := rfl

/-- If color `a` is missing at `v`, then `v` has at most one neighbor
    in the αβ-Kempe subgraph (only the `b`-edge can contribute). -/
lemma kempeSubgraph_neighborSet_ncard_le_one_of_missing_left
    (c : G.lineGraph.Coloring α) (a b : α) (v : V)
    (ha : a ∈ missingColors c v) :
    ((kempeSubgraph c a b).neighborSet v).ncard ≤ 1 := by
  set N_b : Set V := {w | ∃ e : G.edgeSet, e.val = s(v, w) ∧ c.toFun e = b} with hN_b_def
  have h_sub : (kempeSubgraph c a b).neighborSet v ⊆ N_b := by
    intro w hw
    obtain ⟨e, he_val, he_col⟩ := hw
    rcases he_col with h | h
    · exfalso
      apply ha
      refine ⟨e, ?_, h⟩
      change v ∈ e.val
      rw [he_val]; exact Sym2.mem_mk_left v w
    · exact ⟨e, he_val, h⟩
  have hNb_sub : N_b.Subsingleton := neighborSet_color_subsingleton c v b
  exact (Set.ncard_le_ncard h_sub hNb_sub.finite).trans (subsingleton_ncard_le_one hNb_sub)

/-- If color `b` is missing at `v`, then `v` has at most one neighbor
    in the αβ-Kempe subgraph (only the `a`-edge can contribute). -/
lemma kempeSubgraph_neighborSet_ncard_le_one_of_missing_right
    (c : G.lineGraph.Coloring α) (a b : α) (v : V)
    (hb : b ∈ missingColors c v) :
    ((kempeSubgraph c a b).neighborSet v).ncard ≤ 1 := by
  set N_a : Set V := {w | ∃ e : G.edgeSet, e.val = s(v, w) ∧ c.toFun e = a} with hN_a_def
  have h_sub : (kempeSubgraph c a b).neighborSet v ⊆ N_a := by
    intro w hw
    obtain ⟨e, he_val, he_col⟩ := hw
    rcases he_col with h | h
    · exact ⟨e, he_val, h⟩
    · exfalso
      apply hb
      refine ⟨e, ?_, h⟩
      change v ∈ e.val
      rw [he_val]; exact Sym2.mem_mk_left v w
  have hNa_sub : N_a.Subsingleton := neighborSet_color_subsingleton c v a
  exact (Set.ncard_le_ncard h_sub hNa_sub.finite).trans (subsingleton_ncard_le_one hNa_sub)


end vizing
