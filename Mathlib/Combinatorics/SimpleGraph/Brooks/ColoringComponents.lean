/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph
open ConnectedComponent Subgraph Walk
variable {n : ℕ}

variable {α β : Type*} {β : Type*} {G : SimpleGraph α}
/-- Given a coloring of each connected component of `G` we can form a coloring of `G` -/
def coloringOfConnectedComponents (h : ∀ (c : G.ConnectedComponent), (G.induce c).Coloring β) :
    G.Coloring β :=
  ⟨fun v ↦ h (G.connectedComponentMk v) _, fun hab heq ↦
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk _).supp).Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    (h (G.connectedComponentMk _)).valid hadj (by simp only [top_adj] at heq; convert heq)⟩

theorem colorable_iff_forall_connectedComponents :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
     fun h ↦ ⟨coloringOfConnectedComponents (fun c ↦ (h c).some)⟩⟩

-- theorem colorable_iff_forall_connectedComponents' :
--     G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c).Colorable n :=
--   ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
--     fun h ↦ ⟨fun v ↦ (h (G.connectedComponentMk v)).some ⟨_, rfl⟩, fun hab heq ↦
--     have := connectedComponentMk_eq_of_adj hab
--     have hadj : (G.induce (G.connectedComponentMk _).supp).Adj ⟨_, rfl⟩
--        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
--     (h (G.connectedComponentMk _)).some.valid hadj (by simp only [top_adj] at heq; convert heq)⟩⟩

lemma ConnectedComponent.induce_connected (c : G.ConnectedComponent) :
    (G.induce c).Connected := by
  rw [connected_induce_iff, connected_iff_forall_exists_walk_subgraph]
  refine ⟨c.nonempty_supp, fun hu hv ↦ ?_⟩
  obtain ⟨w⟩ := ConnectedComponent.exact (hv ▸ hu)
  use w
  induction w with
  | nil => simpa
  | cons h p ih =>
    rw [Walk.toSubgraph, sup_le_iff]
    refine ⟨subgraphOfAdj_le_of_adj _ ?_, ih (hu ▸ (connectedComponentMk_eq_of_adj h).symm) hv⟩
    simpa using ⟨hu, hu ▸ (connectedComponentMk_eq_of_adj h).symm, h⟩

-- /-- `G` is `n`-colorable iff all its induced connected subgraphs are `n`-colorable -/
-- theorem colorable_iff_forall_induced_connected :
--     (∀ s, (G.induce s).Connected → (G.induce s).Colorable n) ↔ G.Colorable n := by
--   constructor <;> intro h
--   · rw [colorable_iff_forall_connectedComponents]
--     exact fun c ↦ h _ c.induce_connected
--   · intro s _
--     obtain ⟨C⟩ := h
--     exact ⟨fun v ↦ (C v.1), fun a ↦ Hom.map_adj C a⟩

lemma two_colorable_iff_forall_loop_not_odd :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), ¬ Odd w.length := by
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponents.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a ↦ (c.induce_connected ⟨_, hv⟩ a).some.length
    intro a b hab he
    apply h _ <| (((c.induce_connected ⟨_, hv⟩ a).some.concat hab).append
                 (c.induce_connected ⟨_, hv⟩ b).some.reverse).map (Embedding.induce c.supp).toHom
    rw [ZMod.natCast_eq_natCast_iff _ _ 2] at he
    rw [length_map, length_append, add_comm, length_concat, length_reverse, Nat.odd_iff,
        Nat.add_mod, ← he, Nat.mod_two_add_succ_mod_two]

end SimpleGraph
