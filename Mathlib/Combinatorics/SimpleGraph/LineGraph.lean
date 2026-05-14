/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# LineGraph

## Main definitions

* `SimpleGraph.lineGraph` is the line graph of a simple graph `G`, with vertices as the edges of `G`
  and two vertices of the line graph adjacent if the corresponding edges share a vertex in `G`.

## Tags

line graph
-/

@[expose] public section

namespace SimpleGraph

variable {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'}

variable (G) in
/--
The line graph of a simple graph `G` has its vertex set as the edges of `G`, and two vertices of
the line graph are adjacent if the corresponding edges share a vertex in `G`.
-/
def lineGraph : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm e₁ e₂ := by intro h; rwa [ne_comm, Set.inter_comm]

lemma lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} :
    (G.lineGraph).Adj e₁ e₂ ↔ e₁ ≠ e₂ ∧ ∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V) := by
  simp [Set.Nonempty, lineGraph]

@[simp] lemma lineGraph_bot : (⊥ : SimpleGraph V).lineGraph = ⊥ := by aesop (add simp lineGraph)

/-- Lift a copy between graphs to an embedding between their line graphs -/
def Copy.toLineGraphEmbedding (f : Copy G G') : G.lineGraph ↪g G'.lineGraph where
  toFun e := ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
  inj' _ _ h := SetCoe.ext <| Sym2.map.injective f.injective <| Subtype.mk.inj h
  map_rel_iff' := by
    simp only [lineGraph, Function.Embedding.coeFn_mk, Sym2.coe_map, ne_eq]
    refine .and ?_ <| Set.image_inter f.injective ▸ Set.image_nonempty
    rw [Subtype.mk.injEq, Subtype.mk.injEq]
    exact Sym2.map.injective f.injective |>.eq_iff.not

theorem IsIndContained.lineGraph (h : G ⊴ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toCopy.toLineGraphEmbedding⟩

theorem IsContained.isIndContained_lineGraph (h : G ⊑ G') : G.lineGraph ⊴ G'.lineGraph :=
  ⟨h.some.toLineGraphEmbedding⟩

/-- Lift a copy between graphs to a copy between their line graphs -/
def Copy.lineGraph (f : Copy G G') : Copy G.lineGraph G'.lineGraph :=
  f.toLineGraphEmbedding.toCopy

theorem IsContained.lineGraph (h : G ⊑ G') : G.lineGraph ⊑ G'.lineGraph :=
  ⟨h.some.lineGraph⟩

/-- Lift an isomorphism between graphs to an isomorphism between their line graphs -/
def Iso.lineGraph (f : G ≃g G') : G.lineGraph ≃g G'.lineGraph where
  toFun := f.toCopy.lineGraph
  invFun := f.symm.toCopy.lineGraph
  left_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  right_inv _ := by simp [Copy.lineGraph, Copy.toLineGraphEmbedding, Sym2.map_map]
  map_rel_iff' := Copy.toLineGraphEmbedding f.toCopy |>.map_rel_iff

open Function.Embedding in
theorem map_lineGraph_le_of_le {G' : SimpleGraph V} (h : G ≤ G') :
    G.lineGraph.map (subtype _) ≤ G'.lineGraph.map (subtype _) := by
  rintro _ _ ⟨hne', ⟨⟨⟩, h₁⟩, ⟨⟨⟩, h₂⟩, ⟨hne, hinter⟩, rfl, rfl⟩
  exact ⟨hne', ⟨⟨_, h h₁⟩, ⟨_, h h₂⟩, ⟨(hne <| Subtype.ext <| Subtype.mk.inj ·), hinter⟩, rfl, rfl⟩⟩

@[deprecated (since := "2026-03-26")] alias IsSubgraph.lineGraph := map_lineGraph_le_of_le

end SimpleGraph
