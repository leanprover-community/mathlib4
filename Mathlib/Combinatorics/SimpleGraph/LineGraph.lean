/-
Copyright (c) 2024 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy

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

/-- Lift a copy between graphs to a copy between their line graphs -/
def Copy.ofLineGraph (f : Copy G G') : Copy G.lineGraph G'.lineGraph where
  toHom := {
    toFun e := ⟨e.val.map f, by rcases e with ⟨⟨⟩, h⟩; exact f.toHom.map_adj h⟩
    map_rel' := fun ⟨hne, hnonempty⟩ ↦ by
      refine ⟨(hne <| SetCoe.ext <| Sym2.map.injective f.injective <| Subtype.mk.inj ·), ?_⟩
      rw [Sym2.coe_map, Sym2.coe_map]
      exact .mono (Set.image_inter_subset f ..) <| .image _ hnonempty
  }
  injective' _ _ h := SetCoe.ext <| Sym2.map.injective f.injective <| Subtype.mk.inj h

/-- Lift an embedding between graphs to an embedding between their line graphs -/
def Embedding.ofLineGraph (f : Copy G G') : G.lineGraph ↪g G'.lineGraph where
  toFun := f.ofLineGraph
  inj' := f.ofLineGraph.injective
  map_rel_iff' := by
    refine ⟨fun ⟨hne, hnonempty⟩ ↦ ⟨(hne <| congrArg _ ·), ?_⟩, (f.ofLineGraph.toHom.map_rel ·)⟩
    simp only [Copy.ofLineGraph, Copy.coe_mk, RelHom.coeFn_mk, Function.Embedding.coeFn_mk,
      Sym2.coe_map] at hnonempty
    exact .of_image <| Set.image_inter f.injective ▸ hnonempty

/-- Lift an isomorphism between graphs to an isomorphism between their line graphs -/
def Iso.ofLineGraph (f : G ≃g G') : G.lineGraph ≃g G'.lineGraph where
  toFun := f.toCopy.ofLineGraph
  invFun := f.symm.toCopy.ofLineGraph
  left_inv _ := by simp [Copy.ofLineGraph, Sym2.map_map]
  right_inv _ := by simp [Copy.ofLineGraph, Sym2.map_map]
  map_rel_iff' := by
    refine ⟨fun h ↦ ?_, (f.toCopy.ofLineGraph.toHom.map_rel ·)⟩
    simpa [Copy.ofLineGraph, Sym2.map_map] using f.symm.toCopy.ofLineGraph.toHom.map_rel h

end SimpleGraph
