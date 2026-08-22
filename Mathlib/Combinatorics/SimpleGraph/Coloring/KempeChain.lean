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
# Kempe Chain Infrastructure for Vizing's Theorem

This file develops the Kempe chain (also called αβ-interchange) machinery
needed for the proof of Vizing's theorem.

## Main definitions

* `incidentEdges G v` — edges of `G` incident to vertex `v`, viewed as vertices
  of `G.lineGraph`.
* `incidentColors c v` — set of colors used by edges incident to `v`.
* `missingColors c v` — set of colors *not* appearing on any edge incident to `v`.
* `kempeSubgraph c a b` — the subgraph of `G` induced by edges colored `a` or `b`.
* `kempeComponent c a b v` — the connected component of `v` in `kempeSubgraph c a b`.
* `swapKempe c a b v` — the coloring obtained by swapping `a ↔ b` on the
  Kempe component of `v`.

## Main results

* `incidentEdges_ncard_eq_degree` — `|incidentEdges G v| = G.degree v`.
* `missingColors_nonempty_of_degree_lt` — with more colors than the degree,
  some color is missing.
* `kempeSubgraph_neighborSet_ncard_le_two` — every vertex has degree ≤ 2 in the
  Kempe subgraph.
* `swapKempe` is a valid coloring; colors outside `{a, b}` are unchanged.
* `recolorEdge_of_missingColors` — recolor a single edge when its new color is
  missing at both endpoints.
* `extendColoring_of_missingColors_both` — extend a partial coloring across one edge.
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

/-! ### Kempe Chain Swap -/

/-- The involution on colors that swaps `a` and `b`, fixing all other colors. -/
def swapColors [DecidableEq α] (a b : α) (x : α) : α :=
  if x = a then b else if x = b then a else x

@[simp] lemma swapColors_a [DecidableEq α] (a b : α) : swapColors a b a = b := by
  unfold swapColors; simp

lemma swapColors_b [DecidableEq α] (a b : α) : swapColors a b b = a := by
  unfold swapColors
  by_cases h : b = a
  · subst h; simp
  · simp [h]

lemma swapColors_other [DecidableEq α] {a b x : α} (ha : x ≠ a) (hb : x ≠ b) :
    swapColors a b x = x := by
  unfold swapColors; simp [ha, hb]

@[simp] lemma swapColors_swapColors [DecidableEq α] (a b x : α) :
    swapColors a b (swapColors a b x) = x := by
  by_cases h₁ : x = a
  · rw [h₁, swapColors_a, swapColors_b]
  · by_cases h₂ : x = b
    · rw [h₂, swapColors_b, swapColors_a]
    · rw [swapColors_other h₁ h₂, swapColors_other h₁ h₂]

lemma swapColors_injective [DecidableEq α] (a b : α) :
    Function.Injective (swapColors a b) := by
  intro x y hxy
  have := congrArg (swapColors a b) hxy
  simpa using this

/-- The αβ-component of `v`: the set of vertices reachable from `v` in the
    Kempe subgraph `kempeSubgraph c a b`. -/
def kempeComponent (c : G.lineGraph.Coloring α) (a b : α) (v : V) : Set V :=
  {w | (kempeSubgraph c a b).Reachable v w}

/-- An edge `e` is in the *swap zone* (relative to vertex `v`) if it is colored
    `a` or `b` and has an endpoint reachable from `v` in the Kempe subgraph. -/
def inSwapZone (c : G.lineGraph.Coloring α) (a b : α) (v : V) (e : G.edgeSet) : Prop :=
  (c.toFun e = a ∨ c.toFun e = b) ∧
  ∃ x ∈ e.val, (kempeSubgraph c a b).Reachable v x

/-- Both endpoints of an αβ-edge in the swap zone are reachable from `v`. -/
lemma inSwapZone.both_endpoints_reachable
    {c : G.lineGraph.Coloring α} {a b : α} {v : V} {e : G.edgeSet}
    (h : inSwapZone c a b v e) {y : V} (hy : y ∈ e.val) :
    (kempeSubgraph c a b).Reachable v y := by
  obtain ⟨h_col, x, hx_e, hx_reach⟩ := h
  by_cases hxy : x = y
  · subst hxy; exact hx_reach
  · have h_e_val : e.val = s(x, y) := by
      obtain ⟨p, q, hpq⟩ : ∃ p q, e.val = s(p, q) := e.val.ind (fun a b => ⟨a, b, rfl⟩)
      rw [hpq] at hx_e hy ⊢
      rw [Sym2.mem_iff] at hx_e hy
      rcases hx_e with rfl | rfl
      · rcases hy with rfl | rfl
        · exact absurd rfl hxy
        · rfl
      · rcases hy with rfl | rfl
        · rw [Sym2.eq_swap]
        · exact absurd rfl hxy
    have h_adj : (kempeSubgraph c a b).Adj x y := ⟨e, h_e_val, h_col⟩
    exact hx_reach.trans h_adj.reachable

/-- Kempe chain recoloring: swap colors `a ↔ b` on every edge in the
    αβ-component of `v`. The result is a valid proper edge coloring of `G`. -/
noncomputable def swapKempe [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) :
    G.lineGraph.Coloring α := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun e => if inSwapZone c a b v e
              then swapColors a b (c.toFun e)
              else c.toFun e) ?_
  intro e₁ e₂ h_adj
  obtain ⟨h_ne, y, hy1, hy2⟩ := h_adj
  have h_c : c.toFun e₁ ≠ c.toFun e₂ := c.valid ⟨h_ne, y, hy1, hy2⟩
  by_cases h1 : inSwapZone c a b v e₁
  · by_cases h2 : inSwapZone c a b v e₂
    · -- Both swapped: injectivity of swap preserves distinctness.
      simp only [if_pos h1, if_pos h2]
      intro hw
      exact h_c (swapColors_injective a b hw)
    · -- e₁ swapped, e₂ not: the swapped color is in {a,b}, forcing e₂
      -- into the swap zone — contradiction.
      simp only [if_pos h1, if_neg h2]
      intro hw
      have h_swap_in_ab :
          swapColors a b (c.toFun e₁) = a ∨ swapColors a b (c.toFun e₁) = b := by
        obtain ⟨hcol, _⟩ := h1
        rcases hcol with hca | hcb
        · rw [hca]; right; exact swapColors_a a b
        · rw [hcb]; left; exact swapColors_b a b
      rw [hw] at h_swap_in_ab
      have hy_reach : (kempeSubgraph c a b).Reachable v y :=
        h1.both_endpoints_reachable hy1
      exact h2 ⟨h_swap_in_ab, y, hy2, hy_reach⟩
  · by_cases h2 : inSwapZone c a b v e₂
    · -- Symmetric case.
      simp only [if_neg h1, if_pos h2]
      intro hw
      have h_swap_in_ab :
          swapColors a b (c.toFun e₂) = a ∨ swapColors a b (c.toFun e₂) = b := by
        obtain ⟨hcol, _⟩ := h2
        rcases hcol with hca | hcb
        · rw [hca]; right; exact swapColors_a a b
        · rw [hcb]; left; exact swapColors_b a b
      rw [← hw] at h_swap_in_ab
      have hy_reach : (kempeSubgraph c a b).Reachable v y :=
        h2.both_endpoints_reachable hy2
      exact h1 ⟨h_swap_in_ab, y, hy1, hy_reach⟩
    · -- Neither swapped: properness inherited from `c`.
      simp only [if_neg h1, if_neg h2]
      exact h_c

/-- Inside the swap zone, colors are swapped. -/
lemma swapKempe_toFun_of_inSwapZone [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) {e : G.edgeSet}
    (he : inSwapZone c a b v e) :
    (swapKempe c a b v).toFun e = swapColors a b (c.toFun e) := by
  classical
  change (if inSwapZone c a b v e then swapColors a b (c.toFun e) else c.toFun e)
        = swapColors a b (c.toFun e)
  rw [if_pos he]

/-- Outside the swap zone, colors are unchanged. -/
lemma swapKempe_toFun_of_not_inSwapZone [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) {e : G.edgeSet}
    (he : ¬ inSwapZone c a b v e) :
    (swapKempe c a b v).toFun e = c.toFun e := by
  classical
  change (if inSwapZone c a b v e then swapColors a b (c.toFun e) else c.toFun e)
        = c.toFun e
  rw [if_neg he]

/-- Non-swap colors `γ ∉ {a, b}` are preserved by `swapKempe`. -/
lemma swapKempe_toFun_eq_iff_of_ne [DecidableEq α]
    (c : G.lineGraph.Coloring α) {a b : α} (v : V) {e : G.edgeSet} {γ : α}
    (hγa : γ ≠ a) (hγb : γ ≠ b) :
    (swapKempe c a b v).toFun e = γ ↔ c.toFun e = γ := by
  classical
  by_cases h_swap : inSwapZone c a b v e
  · rw [swapKempe_toFun_of_inSwapZone c a b v h_swap]
    constructor
    · intro h
      have := congrArg (swapColors a b) h
      rwa [swapColors_swapColors, swapColors_other hγa hγb] at this
    · intro h
      rw [h, swapColors_other hγa hγb]
  · rw [swapKempe_toFun_of_not_inSwapZone c a b v h_swap]

/-- `incidentColors` membership for non-swap colors is preserved by `swapKempe`. -/
lemma mem_incidentColors_swapKempe_iff_of_ne [DecidableEq α]
    (c : G.lineGraph.Coloring α) {a b : α} (v : V) (w : V) {γ : α}
    (hγa : γ ≠ a) (hγb : γ ≠ b) :
    γ ∈ incidentColors (swapKempe c a b v) w ↔ γ ∈ incidentColors c w := by
  unfold incidentColors incidentEdges
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, hw_e, h_col⟩
    exact ⟨e, hw_e, (swapKempe_toFun_eq_iff_of_ne c v hγa hγb).mp h_col⟩
  · rintro ⟨e, hw_e, h_col⟩
    exact ⟨e, hw_e, (swapKempe_toFun_eq_iff_of_ne c v hγa hγb).mpr h_col⟩

/-- `missingColors` membership for non-swap colors is preserved by `swapKempe`. -/
lemma mem_missingColors_swapKempe_iff_of_ne [DecidableEq α]
    (c : G.lineGraph.Coloring α) {a b : α} (v : V) (w : V) {γ : α}
    (hγa : γ ≠ a) (hγb : γ ≠ b) :
    γ ∈ missingColors (swapKempe c a b v) w ↔ γ ∈ missingColors c w := by
  unfold missingColors
  simp only [Set.mem_compl_iff]
  exact not_iff_not.mpr (mem_incidentColors_swapKempe_iff_of_ne c v w hγa hγb)

/-- At a vertex unreachable from `v`, no incident edge is in the swap zone,
    so `missingColors` is unchanged by `swapKempe`. -/
lemma missingColors_swapKempe_of_not_reachable [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) {w : V}
    (h_unreach : ¬ (kempeSubgraph c a b).Reachable v w) :
    missingColors (swapKempe c a b v) w = missingColors c w := by
  classical
  have h_inc_eq : incidentColors (swapKempe c a b v) w = incidentColors c w := by
    ext γ
    unfold incidentColors incidentEdges
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨e, hw_e, h_col⟩
      have h_not_swap : ¬ inSwapZone c a b v e := by
        intro h_swap
        exact h_unreach (h_swap.both_endpoints_reachable hw_e)
      rw [swapKempe_toFun_of_not_inSwapZone c a b v h_not_swap] at h_col
      exact ⟨e, hw_e, h_col⟩
    · rintro ⟨e, hw_e, h_col⟩
      have h_not_swap : ¬ inSwapZone c a b v e := by
        intro h_swap
        exact h_unreach (h_swap.both_endpoints_reachable hw_e)
      refine ⟨e, hw_e, ?_⟩
      rw [swapKempe_toFun_of_not_inSwapZone c a b v h_not_swap]
      exact h_col
  unfold missingColors
  rw [h_inc_eq]

/-! ### Single-Edge Recoloring -/

set_option linter.unusedDecidableInType false in
/-- Recolor a single edge `e_uv` to color `γ`, when `γ` is missing at both
    endpoints. Returns a coloring with `c'(e_uv) = γ` and all other edges
    unchanged. -/
lemma recolorEdge_of_missingColors
    (c : G.lineGraph.Coloring α)
    (e_uv : G.edgeSet) {u v : V} (he_uv : e_uv.val = s(u, v))
    (γ : α)
    (h_γ_u : γ ∈ missingColors c u)
    (h_γ_v : γ ∈ missingColors c v) :
    ∃ c' : G.lineGraph.Coloring α,
      c'.toFun e_uv = γ ∧
      ∀ e' : G.edgeSet, e' ≠ e_uv → c'.toFun e' = c.toFun e' := by
  classical
  refine ⟨SimpleGraph.Coloring.mk
    (fun e => if e = e_uv then γ else c.toFun e) ?_, ?_, ?_⟩
  · intro f₁ f₂ h_adj
    obtain ⟨h_ne, y, hy1, hy2⟩ := h_adj
    by_cases h1 : f₁ = e_uv
    · have h2 : f₂ ≠ e_uv := fun heq => h_ne (h1.trans heq.symm)
      simp only [h1, if_neg h2]
      have hy1' : y ∈ e_uv.val := h1 ▸ hy1
      rw [he_uv, Sym2.mem_iff] at hy1'
      rcases hy1' with rfl | rfl
      · intro heq; exact h_γ_u ⟨f₂, hy2, heq.symm⟩
      · intro heq; exact h_γ_v ⟨f₂, hy2, heq.symm⟩
    · by_cases h2 : f₂ = e_uv
      · simp only [if_neg h1, h2]
        have hy2' : y ∈ e_uv.val := h2 ▸ hy2
        rw [he_uv, Sym2.mem_iff] at hy2'
        rcases hy2' with rfl | rfl
        · intro heq; exact h_γ_u ⟨f₁, hy1, heq⟩
        · intro heq; exact h_γ_v ⟨f₁, hy1, heq⟩
      · simp only [if_neg h1, if_neg h2]
        exact c.valid ⟨h_ne, y, hy1, hy2⟩
  · change (if e_uv = e_uv then γ else c.toFun e_uv) = γ
    rw [if_pos rfl]
  · intro e' h_ne
    change (if e' = e_uv then γ else c.toFun e') = c.toFun e'
    rw [if_neg h_ne]

/-! ### Edge Extension via a Missing Color -/

set_option linter.unusedDecidableInType false in

/-- If `γ` is missing at both endpoints of `e_uv` in a coloring of `G − {e_uv}`,
    then the coloring extends to all of `G`. -/
lemma extendColoring_of_missingColors_both
    (e_uv : G.edgeSet) {u v : V} (he_uv : e_uv.val = s(u, v))
    (c : (G.deleteEdges {e_uv.val}).lineGraph.Coloring α)
    (γ : α)
    (h_γ_u : γ ∈ missingColors c u)
    (h_γ_v : γ ∈ missingColors c v) :
    Nonempty (G.lineGraph.Coloring α) := by
  classical
  let lift : ∀ f : G.edgeSet, f ≠ e_uv → (G.deleteEdges {e_uv.val}).edgeSet :=
    fun f h => ⟨f.val, by
      rw [SimpleGraph.edgeSet_deleteEdges]
      refine ⟨f.property, ?_⟩
      intro hmem
      exact h (Subtype.ext hmem)⟩
  let newColor : G.edgeSet → α := fun f =>
    if h : f = e_uv then γ else c.toFun (lift f h)
  refine ⟨SimpleGraph.Coloring.mk newColor ?_⟩
  intro f₁ f₂ h_adj
  obtain ⟨h_ne, y, hy1, hy2⟩ := h_adj
  by_cases h1 : f₁ = e_uv
  · have h2 : f₂ ≠ e_uv := fun heq => h_ne (h1.trans heq.symm)
    simp only [newColor, h1, dif_pos rfl, dif_neg h2]
    have hy1' : y ∈ e_uv.val := h1 ▸ hy1
    rw [he_uv, Sym2.mem_iff] at hy1'
    rcases hy1' with rfl | rfl
    · intro heq; apply h_γ_u; exact ⟨lift f₂ h2, hy2, heq.symm⟩
    · intro heq; apply h_γ_v; exact ⟨lift f₂ h2, hy2, heq.symm⟩
  · by_cases h2 : f₂ = e_uv
    · simp only [newColor, dif_neg h1, h2, dif_pos rfl]
      have hy2' : y ∈ e_uv.val := h2 ▸ hy2
      rw [he_uv, Sym2.mem_iff] at hy2'
      rcases hy2' with rfl | rfl
      · intro heq; apply h_γ_u; exact ⟨lift f₁ h1, hy1, heq⟩
      · intro heq; apply h_γ_v; exact ⟨lift f₁ h1, hy1, heq⟩
    · simp only [newColor, dif_neg h1, dif_neg h2]
      apply c.valid
      refine ⟨?_, y, hy1, hy2⟩
      intro h_lift_eq
      apply h_ne
      apply Subtype.ext
      change (lift f₁ h1).val = (lift f₂ h2).val
      exact congrArg Subtype.val h_lift_eq

end vizing
