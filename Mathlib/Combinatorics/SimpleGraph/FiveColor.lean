/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.MinorMap

/-!
# Five color theorem
-/

namespace SimpleGraph

universe u
variable {V : Type u}

/--
The statement that every minor of the graph `G` has a vertex of degree at most 5.

This is implied by planarity. We use this (weaker) condition instead for greater generality, and to
work around the lack of planar graphs in mathlib.
-/
def AllMinorsMinDegreeLE5 {V : Type u} (G : SimpleGraph V) :=
  ∀ {W : Type u} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj],
    MinorMap H G → H.minDegree ≤ 5

/-
def mergeVertex [DecidableEq V] (G : SimpleGraph V) (s t : V) : SimpleGraph { x // x ≠ s } where
  Adj x y :=
    if x = t ∧ ↑y ≠ t then G.Adj s y ∨ G.Adj t y else
    if ↑x ≠ t ∧ y = t then G.Adj s x ∨ G.Adj t x else
    G.Adj x y
  symm x y := by
    by_cases hx : x = t <;>
    by_cases hy : y = t <;>
    { simp [hx, hy]; try exact fun h => G.symm h }

def fiveColorMinorConstruction {V : Type u} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  (v v₁ v₂ : V) [DecidableRel G.Adj] :
  SimpleGraph { x // x ≠ v ∧ x ≠ v₂ } where
    Adj x y := (G.mergeVertex v₂ v₁).Adj ⟨x.val, x.property.right⟩ ⟨y.val, y.property.right⟩
    symm _ _ h := (G.mergeVertex v₂ v₁).symm h

def fiveColorMinorConstruction.minorMap {V : Type u} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
  (v v₁ v₂ : V) [DecidableRel G.Adj] : MinorMap (fiveColorMinorConstruction G v v₁ v₂) G where
  toFun x := if ↑x = v₁ then {v₁, v₂} else {↑x}
  connected := sorry
  disjoint := sorry
  neighbor := sorry
-/

/-
 (hv : G.degree v = 5)
  (hv₁ : G.Adj v v₁) (hv₂ : G.Adj v v₂) (hv₁₂ : ¬ G.Adj v₁ v₂)
-/

private theorem fiveColor_aux {V : Type u} [DecidableEq V] [Fintype V]
  {n : ℕ} (h_card : n = Fintype.card V)
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (h_allMinorsMinDegreeLE5 : G.AllMinorsMinDegreeLE5)
  (h_k6NotMinor : IsEmpty (MinorMap (⊤ : SimpleGraph (Fin 6)) G))
  : G.Colorable 5 := by
  induction' n using Nat.strong_induction_on with n ih generalizing V G
  cases le_or_lt n 5 with
  | inl h_le =>
    exact Colorable.mono (h_card ▸ h_le) <| colorable_of_fintype G
  | inr h_lt =>
    have h_degree_le_5 := h_allMinorsMinDegreeLE5 <| MinorMap.id G
    haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
    rw [hv] at h_degree_le_5; clear hv
    let G' : SimpleGraph { x // x ≠ v } := G.induce { x | x ≠ v }
    cases lt_or_eq_of_le h_degree_le_5 with
    | inl h_degree_lt_5 =>
      have G'_to_G : MinorMap G' G := MinorMap.ofEmbedding (Embedding.induce _)
      have colorable_G' := ih (Fintype.card V - 1) (by omega) (Set.card_ne_eq v |>.symm)
        (fun H_to_G' => h_allMinorsMinDegreeLE5 <| H_to_G'.comp G'_to_G)
        ⟨fun K6_to_G' => h_k6NotMinor.elim <| K6_to_G'.comp G'_to_G⟩
      exact colorable_of_degree_lt colorable_G' h_degree_lt_5
    | inr h_degree_eq_5 =>
      let vertices : Finset V := insert v (G.neighborFinset v)
      have vertices_card : vertices.card = 6 := by simpa using h_degree_eq_5
      by_cases h : G.IsClique vertices
      · rw [G.isClique_iff_induce_eq] at h
        have vertices_to_G : _ ↪g G := Embedding.induce vertices
        rw [h] at vertices_to_G
        have vertices_to_K6 := SimpleGraph.Iso.completeGraph (Fintype.equivFin vertices)
        rw [show Fintype.card vertices = 6 by sorry] at vertices_to_K6
        have K6_to_G : (⊤ : SimpleGraph (Fin 6)) ↪g G :=
          vertices_to_G.comp vertices_to_K6.symm.toEmbedding
        exact h_k6NotMinor.elim <| MinorMap.ofEmbedding K6_to_G
      · dsimp [IsClique, Set.Pairwise] at h
        push_neg at h
        obtain ⟨v₁, hv₁, v₂, hv₂, h_v₁_ne_v₂, h_not_adj_v₁_v₂⟩ := h
        sorry

theorem fiveColor {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
  (h_allMinorsMinDegreeLE5 : G.AllMinorsMinDegreeLE5)
  (h_k6NotMinor : IsEmpty (MinorMap (⊤ : SimpleGraph (Fin 6)) G))
  : G.Colorable 5 := fiveColor_aux rfl h_allMinorsMinDegreeLE5 h_k6NotMinor

end SimpleGraph
