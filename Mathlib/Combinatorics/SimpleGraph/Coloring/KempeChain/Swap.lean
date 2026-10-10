/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeChain.Basic

/-!
# Kempe Chain Swaps

This file defines color swaps along a Kempe component and proves that swapping
preserves proper edge colorings.
-/

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

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
      simp only [ite_eq_left h1, ite_eq_left h2]
      intro hw
      exact h_c (swapColors_injective a b hw)
    · -- e₁ swapped, e₂ not: the swapped color is in {a,b}, forcing e₂
      -- into the swap zone — contradiction.
      simp only [ite_eq_left h1, ite_eq_right h2]
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
      simp only [ite_eq_right h1, ite_eq_left h2]
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
      simp only [ite_eq_right h1, ite_eq_right h2]
      exact h_c

/-- Inside the swap zone, colors are swapped. -/
lemma swapKempe_toFun_of_inSwapZone [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) {e : G.edgeSet}
    (he : inSwapZone c a b v e) :
    (swapKempe c a b v).toFun e = swapColors a b (c.toFun e) := by
  classical
  change (if inSwapZone c a b v e then swapColors a b (c.toFun e) else c.toFun e)
        = swapColors a b (c.toFun e)
  rw [ite_eq_left he]

/-- Outside the swap zone, colors are unchanged. -/
lemma swapKempe_toFun_of_not_inSwapZone [DecidableEq α]
    (c : G.lineGraph.Coloring α) (a b : α) (v : V) {e : G.edgeSet}
    (he : ¬ inSwapZone c a b v e) :
    (swapKempe c a b v).toFun e = c.toFun e := by
  classical
  change (if inSwapZone c a b v e then swapColors a b (c.toFun e) else c.toFun e)
        = c.toFun e
  rw [ite_eq_right he]

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
  simp only [Set.mem_image, Set.mem_ofPred_eq]
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
    simp only [Set.mem_image, Set.mem_ofPred_eq]
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


end vizing
