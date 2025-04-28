/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Brooks.OddCycles

namespace SimpleGraph
open ConnectedComponent Subgraph List Walk
variable {n : ℕ}

variable {α β : Type*} {β : Type*} {G : SimpleGraph α}
/-- Given a coloring of each component of `G` we can form a coloring of `G` -/
def coloringOfComponents (h : ∀ (c : G.ConnectedComponent), (G.induce c).Coloring β) :
    G.Coloring β := by
  exact ⟨fun v ↦ h (G.connectedComponentMk v) ⟨v, rfl⟩, by
    simp only [top_adj]
    intro a b hab heq
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk a).supp).Adj ⟨a, rfl⟩
       ⟨b, ((G.connectedComponentMk a).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    exact (h _).valid hadj (by convert heq)⟩

theorem colorable_iff_forall_connectedComponents  :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
     fun h ↦ ⟨coloringOfComponents (fun c ↦ (h c).some)⟩⟩

lemma ConnectedComponent.induce_supp_connected (c : G.ConnectedComponent) :
    (G.induce c).Connected := by
  rw [connected_induce_iff, connected_iff_forall_exists_walk_subgraph]
  refine ⟨c.nonempty_supp,fun hu hv ↦ ?_⟩
  obtain ⟨w⟩ := ConnectedComponent.exact (hv ▸ hu)
  use w
  induction w with
  | nil => simpa
  | cons h p ih =>
    rw [Walk.toSubgraph, sup_le_iff]
    refine ⟨?_, ih (hu ▸ (connectedComponentMk_eq_of_adj h).symm) hv⟩
    apply subgraphOfAdj_le_of_adj
    simpa using ⟨hu, hu ▸ (connectedComponentMk_eq_of_adj h).symm, h⟩

/-- `G` is `n`-colorable iff all its induced connected subgraphs are `n`-colorable -/
theorem colorable_iff_forall_induced_connected :
    (∀ s, (G.induce s).Connected → (G.induce s).Colorable n) ↔ G.Colorable n := by
  constructor <;> intro h
  · rw [colorable_iff_forall_connectedComponents]
    exact fun c ↦ h _ c.induce_supp_connected
  · intro s _
    obtain ⟨C⟩ := h
    exact ⟨fun v ↦ (C v.1), fun a ↦ Hom.map_adj C a⟩

lemma two_colorable_of_no_odd_closed_walk (ho : ∀ u, ∀ (w : G.Walk u u), ¬ Odd w.length) :
    G.Colorable 2 := by
  rw [colorable_iff_forall_connectedComponents]
  intro c
  obtain ⟨v, hv⟩ := c.nonempty_supp
  use fun a ↦ ((c.induce_supp_connected ⟨_, hv⟩ a).some.length : Fin 2)
  intro a b hab heq
  apply ho v <| ((((c.induce_supp_connected ⟨_, hv⟩ a).some).concat hab).append
               (c.induce_supp_connected ⟨_, hv⟩ b).some.reverse).map (Embedding.induce c.supp).toHom
  rw [Walk.length_map, Walk.length_append, add_comm, Walk.length_concat, Walk.length_reverse,
    ← add_assoc, Nat.odd_iff]
  have := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 heq
  omega

end SimpleGraph
