/-
Copyright (c) 2025 John Talbot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Data.ZMod.Basic
/-!
## Main definition

* Given a `Coloring β` for each connected component of the
graph `G` define `coloringOfConnectedComponents` to be the `G.Coloring β`.

Hence prove that a graph is `n` - colorable iff each of its components are.

In particular prove that `G` is 2 - colorable iff it contains no odd length loop (closed walk).
-/
namespace SimpleGraph

variable {α β : Type*} {β : Type*} {G : SimpleGraph α}

open ConnectedComponent

/-- Given a coloring of each connected component of `G` we can form a coloring of `G` -/
def coloringOfConnectedComponents (h : ∀ (c : G.ConnectedComponent), (G.induce c).Coloring β) :
    G.Coloring β :=
  ⟨fun v ↦ h (G.connectedComponentMk v) _, fun hab heq ↦
    have := connectedComponentMk_eq_of_adj hab
    have hadj : (G.induce (G.connectedComponentMk _).supp).Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    (h (G.connectedComponentMk _)).valid hadj (by simp only [top_adj] at heq; convert heq)⟩

theorem colorable_iff_forall_connectedComponents {n : ℕ} :
    G.Colorable n ↔ ∀ c : G.ConnectedComponent, (G.induce c).Colorable n :=
  ⟨fun ⟨C⟩ _ ↦ ⟨fun v ↦ C v.1, fun h h1 ↦ C.valid h h1⟩,
     fun h ↦ ⟨coloringOfConnectedComponents (fun c ↦ (h c).some)⟩⟩

open Walk Subgraph

lemma two_colorable_iff_forall_loop_not_odd :
    G.Colorable 2 ↔ ∀ u, ∀ (w : G.Walk u u), ¬ Odd w.length := by
  constructor <;> intro h
  · intro _ w ho
    have := (w.three_le_chromaticNumber_of_odd_loop ho).trans h.chromaticNumber_le
    norm_cast
  · apply colorable_iff_forall_connectedComponents.2
    intro c
    obtain ⟨_, hv⟩ := c.nonempty_supp
    use fun a ↦ (c.connected_induce ⟨_, hv⟩ a).some.length
    intro a b hab he
    apply h _ <| (((c.connected_induce ⟨_, hv⟩ a).some.concat hab).append
                 (c.connected_induce ⟨_, hv⟩ b).some.reverse).map (Embedding.induce c.supp).toHom
    rw [ZMod.natCast_eq_natCast_iff _ _ 2] at he
    rw [length_map, length_append, add_comm, length_concat, length_reverse, Nat.odd_iff,
        Nat.add_mod, ← he, Nat.mod_two_add_succ_mod_two]

end SimpleGraph
