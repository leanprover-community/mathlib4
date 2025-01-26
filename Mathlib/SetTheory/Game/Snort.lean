/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
import Mathlib.SetTheory.Game.State
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph

/-!
# Snort as a combinatorial game.

We are implementing a "variant" when instead of coloring the vertex it gets removed instead and
adjacent vertices are tinted in players color. Vertices that would be tinted in both colors are
removed as well though without any further tinting. Player can move only in a blank vertex or
in a vertex tinted in their own color.
-/

namespace SetTheory

namespace PGame

namespace Snort

universe u

inductive Color : Type where
  | Blank : Color
  | Blue : Color
  | Red : Color

structure Position (V : Type u) where
  graph : SimpleGraph.Finsubgraph (completeGraph V)
  getColor : V → Color

noncomputable instance {V : Type u} : DecidableEq (Position V) :=
  Classical.typeDecidableEq (Position V)

def left {V : Type u} (p : Position V) : Set V :=
  {v | v ∈ p.graph.val.verts ∧ (p.getColor v = Color.Blue ∨ p.getColor v = Color.Blank)}

noncomputable def leftFin {V : Type u} (p : Position V)
  : Finset V :=
  have : (v : V) → (c : Color) → Decidable (p.getColor v = c) :=
    fun v c => Classical.propDecidable (p.getColor v = c)
  Finset.filter
    (fun v => p.getColor v = Color.Blue ∨ p.getColor v = Color.Blank)
    p.graph.property.toFinset

def right {V : Type u} (p : Position V) : Set V :=
  {v | v ∈ p.graph.val.verts ∧ (p.getColor v = Color.Red ∨ p.getColor v = Color.Blank)}

noncomputable def rightFin {V : Type u} (p : Position V)
  : Finset V :=
  have : (v : V) → (c : Color) → Decidable (p.getColor v = c) :=
    fun v c => Classical.propDecidable (p.getColor v = c)
  Finset.filter
    (fun v => p.getColor v = Color.Red ∨ p.getColor v = Color.Blank)
    p.graph.property.toFinset

def Position.deleteVerts
  {V : Type u} (p : Position V) (s: Set V)
  : Position V :=
  ⟨ ⟨p.graph.val.deleteVerts s, Set.Finite.diff p.graph.property⟩
  , p.getColor
  ⟩

noncomputable def leftMove {V : Type u} (p : Position V) (m : V) : Position V :=
  have : (v : V) → Decidable (v ∈ p.graph.val.neighborSet m) := fun v =>
    Classical.propDecidable (v ∈ p.graph.val.neighborSet m)
  -- Remove vertex we just moved in and if the move vertex was adjacent to a vertex of opposite
  -- tint then we remove it as well otherwise it would be tinted in both colors so no player can
  -- move
  let without_double_tinted :=
    p.deleteVerts ({v | v ∈ p.graph.val.neighborSet m ∧ p.getColor v = Color.Red} ∪ {m})
  -- Now every vertex that was adjacent to move vertex is either our tint or blank so we can tint it
  ⟨ without_double_tinted.graph
  , fun v =>
      if v ∈ p.graph.val.neighborSet m
      then Color.Blue
      else p.getColor v
  ⟩

noncomputable def rightMove {V : Type u} (p : Position V) (m : V) : Position V :=
  have : (v : V) → Decidable (v ∈ p.graph.val.neighborSet m) := fun v =>
    Classical.propDecidable (v ∈ p.graph.val.neighborSet m)
  let without_double_tinted :=
    p.deleteVerts ({v | v ∈ p.graph.val.neighborSet m ∧ p.getColor v = Color.Blue} ∪ {m})
  ⟨ without_double_tinted.graph
  , fun v =>
      if v ∈ p.graph.val.neighborSet m
      then Color.Red
      else p.getColor v
  ⟩

-- TODO: golf proofs
noncomputable instance state {V : Type u} : State (Position V) where
  turnBound p := p.graph.property.toFinset.card
  l p := Finset.image (leftMove p) (leftFin p)
  r p := Finset.image (rightMove p) (rightFin p)
  left_bound := by
    intro s t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨v, ⟨v_in_left, h_sv⟩⟩ := ht
    simp only [SimpleGraph.completeGraph_eq_top]
    rw [<-h_sv]
    unfold leftMove
    simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.Subgraph.mem_neighborSet,
               Set.union_singleton]
    refine Finset.card_lt_card ?_
    refine Set.Finite.toFinset_ssubset_toFinset.mpr ?_
    unfold Position.deleteVerts
    simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.Subgraph.induce_verts]
    refine Set.ssubset_iff_subset_ne.mpr ?_
    refine And.intro (Set.diff_subset) ?_
    simp only [ne_eq, sdiff_eq_left]
    unfold Disjoint
    intro h_d
    simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff] at h_d
    have h_v := v_in_left
    unfold leftFin at h_v
    simp only [SimpleGraph.completeGraph_eq_top, Finset.mem_filter, Set.Finite.mem_toFinset] at h_v
    obtain ⟨v_in_verts, v_color⟩ := h_v
    have singleton_empty := h_d
      (Set.singleton_subset_iff.mpr v_in_verts)
      (Set.singleton_subset_iff.mpr
        (Set.mem_insert v {v_1 | s.graph.val.Adj v v_1 ∧ s.getColor v_1 = Color.Red}))
    exact Set.singleton_ne_empty v singleton_empty
  right_bound := by
    intro s t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨v, ⟨v_in_right, h_sv⟩⟩ := ht
    simp only [SimpleGraph.completeGraph_eq_top]
    rw [<-h_sv]
    unfold rightMove
    simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.Subgraph.mem_neighborSet,
               Set.union_singleton]
    refine Finset.card_lt_card ?_
    refine Set.Finite.toFinset_ssubset_toFinset.mpr ?_
    unfold Position.deleteVerts
    simp only [SimpleGraph.completeGraph_eq_top, SimpleGraph.Subgraph.induce_verts]
    refine Set.ssubset_iff_subset_ne.mpr ?_
    refine And.intro (Set.diff_subset) ?_
    simp only [ne_eq, sdiff_eq_left]
    unfold Disjoint
    intro h_d
    simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff] at h_d
    have h_v := v_in_right
    unfold rightFin at h_v
    simp only [SimpleGraph.completeGraph_eq_top, Finset.mem_filter, Set.Finite.mem_toFinset] at h_v
    obtain ⟨v_in_verts, v_color⟩ := h_v
    have singleton_empty := h_d
      (Set.singleton_subset_iff.mpr v_in_verts)
      (Set.singleton_subset_iff.mpr
        (Set.mem_insert v {v_1 | s.graph.val.Adj v v_1 ∧ s.getColor v_1 = Color.Blue}))
    exact Set.singleton_ne_empty v singleton_empty

noncomputable def snort {V : Type u} (p : Position V) : PGame := PGame.ofState p

noncomputable def snort.zero : PGame :=
  snort
  ⟨ ⟨ ( completeGraph Empty).toSubgraph (completeGraph Empty) (fun ⦃_ _⦄ a => a )
      , Set.toFinite (SimpleGraph.toSubgraph (completeGraph Empty) fun ⦃_ _⦄ a ↦ a).verts
      ⟩
  , Empty.elim
  ⟩

noncomputable def snort.one : PGame :=
  snort
  ⟨ ⟨( completeGraph Unit).toSubgraph (completeGraph Unit) (fun ⦃_ _⦄ a => a )
     , Set.toFinite (SimpleGraph.toSubgraph (completeGraph Unit) fun ⦃_ _⦄ a ↦ a).verts ⟩
  , fun _ => Color.Blue
  ⟩

-- FIXME: Borked because Decidable (snort.one ≈ 1) does not hold
-- #eval decide (snort.one ≈ 1)

end Snort

end PGame

end SetTheory
