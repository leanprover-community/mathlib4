/-
Copyright (c) 2026 Yiyang He, Daniel Raggi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yiyang He, Daniel Raggi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.KempeChain.Swap

/-!
# Kempe Chain Recoloring

This file proves recoloring lemmas used to extend partial edge colorings.
-/

@[expose] public section

namespace vizing

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

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
      simp only [h1, ite_eq_right h2]
      have hy1' : y ∈ e_uv.val := h1 ▸ hy1
      rw [he_uv, Sym2.mem_iff] at hy1'
      rcases hy1' with rfl | rfl
      · intro heq; exact h_γ_u ⟨f₂, hy2, heq.symm⟩
      · intro heq; exact h_γ_v ⟨f₂, hy2, heq.symm⟩
    · by_cases h2 : f₂ = e_uv
      · simp only [ite_eq_right h1, h2]
        have hy2' : y ∈ e_uv.val := h2 ▸ hy2
        rw [he_uv, Sym2.mem_iff] at hy2'
        rcases hy2' with rfl | rfl
        · intro heq; exact h_γ_u ⟨f₁, hy1, heq⟩
        · intro heq; exact h_γ_v ⟨f₁, hy1, heq⟩
      · simp only [ite_eq_right h1, ite_eq_right h2]
        exact c.valid ⟨h_ne, y, hy1, hy2⟩
  · change (if e_uv = e_uv then γ else c.toFun e_uv) = γ
    rw [ite_eq_left rfl]
  · intro e' h_ne
    change (if e' = e_uv then γ else c.toFun e') = c.toFun e'
    rw [ite_eq_right h_ne]

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
    simp only [newColor, h1, dite_eq_left rfl, dite_eq_right h2]
    have hy1' : y ∈ e_uv.val := h1 ▸ hy1
    rw [he_uv, Sym2.mem_iff] at hy1'
    rcases hy1' with rfl | rfl
    · intro heq; apply h_γ_u; exact ⟨lift f₂ h2, hy2, heq.symm⟩
    · intro heq; apply h_γ_v; exact ⟨lift f₂ h2, hy2, heq.symm⟩
  · by_cases h2 : f₂ = e_uv
    · simp only [newColor, dite_eq_right h1, h2, dite_eq_left rfl]
      have hy2' : y ∈ e_uv.val := h2 ▸ hy2
      rw [he_uv, Sym2.mem_iff] at hy2'
      rcases hy2' with rfl | rfl
      · intro heq; apply h_γ_u; exact ⟨lift f₁ h1, hy1, heq⟩
      · intro heq; apply h_γ_v; exact ⟨lift f₁ h1, hy1, heq⟩
    · simp only [newColor, dite_eq_right h1, dite_eq_right h2]
      apply c.valid
      refine ⟨?_, y, hy1, hy2⟩
      intro h_lift_eq
      apply h_ne
      apply Subtype.ext
      change (lift f₁ h1).val = (lift f₂ h2).val
      exact congrArg Subtype.val h_lift_eq

end vizing
