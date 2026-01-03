/-
Copyright (c) 2025 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Edge coloring

This module defines edge colorings of simple graphs.
An edge coloring of a graph is an assignment of "colors" to all of its edges such that edges that
share a vertex have different colors.
A coloring can be represented as a homomorphism from the graph's edge set into a complete graph,
whose vertices represent the available colors.

## Main definitions

* `G.EdgeColoring α` is the type of `α`-edge-colorings of a simple graph `G`,
  with `α` being the set of available colors.
  The type is defined to be a coloring of `G.lineGraph`,
  and colorings have a coercion to `G.EdgeLabeling α`.

* `G.EdgeColorableWith α` is the proposition that `G` is `α`-edge-colorable,
  which is whether there exists an edge-coloring of `G` using colors from `α`.

* `G.EdgeColorable n` is the proposition that `G` is `n`-edge-colorable,
  which is whether there exists an edge-coloring of `G` with at most `n` colors.

* `G.chromaticIndex` is the minimal `n` such that `G` is `n`-edge-colorable,
  or `⊤` if it cannot be colored with finitely many colors.
  (Cardinal-valued chromatic numbers are more niche, so we stick to `ℕ∞`.)
  We write `G.chromaticIndex ≠ ⊤` to mean a graph is colorable with finitely many colors.
-/

@[expose] public section

namespace SimpleGraph

open Fintype

variable {V V' α β : Type*} {G H : SimpleGraph V} {G' : SimpleGraph V'} {n m : ℕ}

variable (G) in
/-- An `α`-edge-coloring of a simple graph `G` is a coloring of `G.lineGraph` -/
abbrev EdgeColoring (α : Type*) := G.lineGraph.Coloring α

/-- `α`-edge-coloring is a special case of `α`-edge-labeling -/
instance : Coe (G.EdgeColoring α) (G.EdgeLabeling α) := ⟨RelHom.toFun⟩

variable (G) in
/-- Whether a graph can be edge-colored using colors from `α` -/
def EdgeColorableWith (α : Type*) : Prop := Nonempty <| G.EdgeColoring α

variable (G n) in
/-- Whether a graph can be edge-colored by at most `n` colors -/
def EdgeColorable : Prop := G.EdgeColorableWith <| Fin n

variable (G) in
/-- The chromatic index of a graph is the minimal number of colors needed to color its edges.
This is `⊤` (infinity) iff `G` isn't edge-colorable with finitely many colors.
If `G` is edge-colorable, then `G.chromaticIndex.toNat` is the `ℕ`-valued chromatic number. -/
noncomputable def chromaticIndex : ℕ∞ := ⨅ n ∈ setOf G.EdgeColorable, (n : ℕ∞)

variable (α) in
/-- The unique coloring of the empty graph -/
def EdgeColoring.ofBot : (⊥ : SimpleGraph V).EdgeColoring α :=
  .mk (fun ⟨_, h⟩ ↦ edgeSet_bot ▸ h |>.elim) (lineGraph_bot ▸ · |>.elim)

variable (α) in
theorem EdgeColorableWith.of_bot : (⊥ : SimpleGraph V).EdgeColorableWith α :=
  ⟨.ofBot _⟩

variable (α) in
@[simp]
lemma edgeColorableWith_iff_of_isEmpty [IsEmpty α] : G.EdgeColorableWith α ↔ G = ⊥ :=
  ⟨fun ⟨C⟩ ↦ edgeSet_eq_empty.mp <| Set.isEmpty_coe_sort.mp C.toFun.isEmpty, (· ▸ .of_bot α)⟩

variable (n) in
theorem EdgeColorable.of_bot : (⊥ : SimpleGraph V).EdgeColorable n :=
  EdgeColorableWith.of_bot _

@[simp]
lemma edgeColorable_zero_iff : G.EdgeColorable 0 ↔ G = ⊥ :=
  edgeColorableWith_iff_of_isEmpty _

variable (V) in
@[simp]
theorem chromaticIndex_bot : (⊥ : SimpleGraph V).chromaticIndex = 0 :=
  have : IsEmpty (⊥ : SimpleGraph V).edgeSet := by simp
  chromaticNumber_eq_zero_of_isEmpty

theorem eq_bot_of_chromaticIndex_eq_zero (h : G.chromaticIndex = 0) : G = ⊥ := by
  simpa using isEmpty_of_chromaticNumber_eq_zero h

/-- Lift an embedding of colors to an embedding of edge colorings -/
def EdgeColoring.ofColorEmbedding (f : α ↪ β) : G.EdgeColoring α ↪ G.EdgeColoring β :=
  recolorOfEmbedding _ f

/-- Lift an isomorphism of colors to an isomorphism of edge colorings -/
def EdgeColoring.ofColorIso (f : α ≃ β) : G.EdgeColoring α ≃ G.EdgeColoring β :=
  recolorOfEquiv _ f

theorem EdgeColorableWith.mono (f : α ↪ β) (hc : G.EdgeColorableWith α) :
    G.EdgeColorableWith β :=
  ⟨.ofColorEmbedding f hc.some⟩

theorem EdgeColorable.mono (h : n ≤ m) (hc : G.EdgeColorable n) : G.EdgeColorable m :=
  Colorable.mono h hc

/-- Edge coloring using the edges themselves as colors, coloring with the identity function -/
def EdgeColoring.id : G.EdgeColoring G.edgeSet :=
  selfColoring _

theorem EdgeColoring.edgeColorable [Fintype α] (C : G.EdgeColoring α) : G.EdgeColorable <| card α :=
  Coloring.colorable C

variable (G) in
theorem EdgeColorable.of_fintype [Fintype G.edgeSet] : G.EdgeColorable <| card G.edgeSet :=
  colorable_of_fintype _

/-- Pre-compose an edge coloring with a line-graph homomorphism -/
def EdgeColoring.ofLineGraphHom (f : G.lineGraph →g G'.lineGraph) (C : G'.EdgeColoring α) :
    G.EdgeColoring α :=
  C.comp f

/-- Pre-compose an edge-coloring with a line-graph homomorphism induced by a copy -/
def EdgeColoring.ofCopy (f : Copy G G') (C : G'.EdgeColoring α) : G.EdgeColoring α :=
  C.ofLineGraphHom f.ofLineGraph.toHom

variable (α) in
/-- Edge-colorings of graphs with isomorphic line-graphs are equivalent -/
def EdgeColoring.ofLineGraphIso (f : G.lineGraph ≃g G'.lineGraph) :
    G.EdgeColoring α ≃ G'.EdgeColoring α where
  toFun C := .ofLineGraphHom f.symm.toHom C
  invFun C' := .ofLineGraphHom f.toHom C'
  left_inv _ := RelHom.ext (congrArg _ <| RelIso.symm_apply_apply f ·)
  right_inv _ := RelHom.ext (congrArg _ <| RelIso.apply_symm_apply f ·)

variable (α) in
/-- Edge-colorings of isomorphic graphs are equivalent -/
def EdgeColoring.ofIso (f : G ≃g G') : G.EdgeColoring α ≃ G'.EdgeColoring α :=
  EdgeColoring.ofLineGraphIso α f.ofLineGraph

theorem EdgeColorableWith.of_lineGraph_hom (f : G.lineGraph →g G'.lineGraph)
    (h : G'.EdgeColorableWith α) : G.EdgeColorableWith α :=
  ⟨h.some.ofLineGraphHom f⟩

theorem EdgeColorableWith.of_isContained (f : G ⊑ G') (h : G'.EdgeColorableWith α) :
    G.EdgeColorableWith α :=
  ⟨h.some.ofCopy f.some⟩

variable (α) in
theorem EdgeColorableWith.of_lineGraph_iso (f : G.lineGraph ≃g G'.lineGraph) :
    G.EdgeColorableWith α ↔ G'.EdgeColorableWith α :=
  ⟨(⟨EdgeColoring.ofLineGraphIso α f ·.some⟩), (⟨EdgeColoring.ofLineGraphIso α f |>.symm ·.some⟩)⟩

variable (α) in
theorem EdgeColorableWith.of_iso (f : G ≃g G') : G.EdgeColorableWith α ↔ G'.EdgeColorableWith α :=
  EdgeColorableWith.of_lineGraph_iso α f.ofLineGraph

theorem EdgeColorable.of_lineGraph_hom (f : G.lineGraph →g G'.lineGraph) (h : G'.EdgeColorable n) :
    G.EdgeColorable n :=
  Colorable.of_hom f h

theorem EdgeColorable.of_isContained (f : G ⊑ G') (h : G'.EdgeColorable n) : G.EdgeColorable n :=
  EdgeColorableWith.of_isContained f h

variable (n) in
theorem EdgeColorable.of_lineGraph_iso (f : G.lineGraph ≃g G'.lineGraph) :
    G.EdgeColorable n ↔ G'.EdgeColorable n :=
  EdgeColorableWith.of_lineGraph_iso _ f

variable (n) in
theorem EdgeColorable.of_iso (f : G ≃g G') : G.EdgeColorable n ↔ G'.EdgeColorable n :=
  EdgeColorableWith.of_iso _ f

theorem chromaticIndex_le_of_lineGraph_hom (f : G.lineGraph →g G'.lineGraph) :
    G.chromaticIndex ≤ G'.chromaticIndex :=
  chromaticNumber_mono_of_hom f

theorem IsContained.chromaticIndex_le (f : G ⊑ G') : G.chromaticIndex ≤ G'.chromaticIndex :=
  chromaticIndex_le_of_lineGraph_hom f.some.ofLineGraph.toHom

theorem chromaticIndex_eq_of_lineGraph_iso (f : G.lineGraph ≃g G'.lineGraph) :
    G.chromaticIndex = G'.chromaticIndex :=
  le_antisymm (chromaticIndex_le_of_lineGraph_hom f) (chromaticIndex_le_of_lineGraph_hom f.symm)

theorem Iso.chromaticIndex_eq (f : G ≃g G') : G.chromaticIndex = G'.chromaticIndex :=
  chromaticIndex_eq_of_lineGraph_iso f.ofLineGraph

/-- Induce an edge-coloring of a subgraph from an edge-coloring of a graph -/
def EdgeColoring.ofIsSubgraph (hle : G ≤ H) (C : H.EdgeColoring α) : G.EdgeColoring α :=
  C.ofCopy <| .ofLE _ _ hle

theorem EdgeColorableWith.anti (hle : G ≤ H) (hc : H.EdgeColorableWith α) : G.EdgeColorableWith α :=
  hc.of_isContained <| .of_le hle

theorem EdgeColorable.anti (hle : G ≤ H) (hc : H.EdgeColorable n) : G.EdgeColorable n :=
  hc.of_isContained <| .of_le hle

theorem chromaticIndex_mono (hle : G ≤ H) : G.chromaticIndex ≤ H.chromaticIndex :=
  IsContained.chromaticIndex_le <| .of_le hle

theorem EdgeColorable.chromaticIndex_le (hc : G.EdgeColorable n) : G.chromaticIndex ≤ n :=
  Colorable.chromaticNumber_le hc

variable (G) in
theorem chromaticIndex_ne_top_iff_exists : G.chromaticIndex ≠ ⊤ ↔ ∃ n, G.EdgeColorable n :=
  chromaticNumber_ne_top_iff_exists

variable (G) in
theorem chromaticIndex_le_iff_edgeColorable : G.chromaticIndex ≤ n ↔ G.EdgeColorable n :=
  chromaticNumber_le_iff_colorable

variable (G) in
theorem chromaticIndex_eq_iff_edgeColorable_not_edgeColorable :
    G.chromaticIndex = n + 1 ↔ G.EdgeColorable (n + 1) ∧ ¬G.EdgeColorable n :=
  chromaticNumber_eq_iff_colorable_not_colorable

variable (G) in
theorem edgeColorable_chromaticIndex_iff :
    G.chromaticIndex ≠ ⊤ ↔ G.EdgeColorable G.chromaticIndex.toNat :=
  ⟨(G.chromaticIndex_ne_top_iff_exists.mp · |>.elim fun _ ↦ colorable_chromaticNumber),
  (G.chromaticIndex_ne_top_iff_exists.mpr ⟨_, ·⟩)⟩

variable (G) in
theorem EdgeColorable.chromaticIndex_of_finite [Finite G.edgeSet] :
    G.EdgeColorable G.chromaticIndex.toNat :=
  colorable_chromaticNumber_of_fintype _

variable (G) in
theorem chromaticIndex_le_one_of_subsingleton [Subsingleton G.edgeSet] : G.chromaticIndex ≤ 1 :=
  chromaticNumber_le_one_of_subsingleton _

theorem chromaticIndex_pos {n : ℕ} (h : G.edgeSet.Nonempty) (hc : G.EdgeColorable n) :
    0 < G.chromaticIndex :=
  have := Set.nonempty_coe_sort.mpr h
  chromaticNumber_pos hc

theorem two_le_chromaticIndex_of_adj {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (h : v ≠ w) :
    2 ≤ G.chromaticIndex :=
  @two_le_chromaticNumber_of_adj _ _ ⟨s(u, v), huv⟩ ⟨s(u, w), huw⟩ ⟨by grind, u, by simp⟩

/-- The subgraph containing all the edges colored with the given color, and all their vertices -/
def EdgeColoring.colorClassSubgraph (C : G.EdgeColoring α) (a : α) : G.Subgraph where
  verts := {u | ∃ (v : V) (hadj : G.Adj u v), C ⟨s(u, v), hadj⟩ = a}
  Adj u v := ∃ (hadj : G.Adj u v), C ⟨s(u, v), hadj⟩ = a
  adj_sub := Exists.fst
  edge_vert := (⟨_, ·⟩)
  symm := fun _ _ ⟨hadj, _⟩ ↦ ⟨hadj.symm, by grind⟩

theorem EdgeColoring.isMatching_colorClassSubgraph (C : G.EdgeColoring α) (a : α) :
    C.colorClassSubgraph a |>.IsMatching := by
  refine fun u ⟨v, hadjv, hv⟩ ↦ ⟨v, ⟨hadjv, hv⟩, fun w ⟨hadjw, hw⟩ ↦ ?_⟩
  by_contra
  exact C.valid ⟨by grind, u, Sym2.mem_mk_left .., Sym2.mem_mk_left ..⟩ <| hv ▸ hw.symm

end SimpleGraph
