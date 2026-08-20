/-
Copyright (c) 2026 Justin Lai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justin Lai
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!

# Star Graphs

## Main definitions

* `SimpleGraph.starGraph r` is the star graph on V centered at r. Every non-center vertex is
  adjacent to r.

## Main statements

* `SimpleGraph.isTree_starGraph` proves the star graph is a tree.


## Tags

star graph
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} (G : SimpleGraph V)

/-- The star graph on `V` centered at `r`: every non-center vertex is adjacent to `r`. -/
def starGraph (r : V) : SimpleGraph V :=
  .fromRel fun v _ ↦ v = r

instance [DecidableEq V] (r : V) : DecidableRel (starGraph r).Adj :=
  inferInstanceAs (DecidableRel fun x y ↦ x ≠ y ∧ (x = r ∨ y = r))

@[simp]
lemma starGraph_adj {r x y : V} : (starGraph r).Adj x y ↔ x ≠ y ∧ (x = r ∨ y = r) := by
  simp [starGraph, fromRel]

@[simp]
lemma isUniversal_starGraph_self {r : V} : (starGraph r).IsUniversal r := by
  intro _ _
  simpa

/-- On (starGraph r), r is adjacent to v iff v ≠ r. -/
lemma starGraph_adj_center_iff {r v : V} : (starGraph r).Adj r v ↔ r ≠ v := by simp

lemma starGraph_center_adj {r v : V} (h : r ≠ v) : (starGraph r).Adj r v :=
  starGraph_adj_center_iff.mpr h

lemma starGraph_center_adj' {r v : V} (h : r ≠ v) : (starGraph r).Adj v r :=
  (starGraph_center_adj h).symm

lemma connected_starGraph (r : V) : (starGraph r).Connected :=
  .of_isUniversal isUniversal_starGraph_self

lemma isAcyclic_starGraph (r : V) : (starGraph r).IsAcyclic := by
  refine isAcyclic_iff_forall_adj_isBridge.mpr fun v w hadj ↦ ?_
  rw [starGraph_adj] at hadj
  wlog! h : v = r
  · rw [Sym2.eq_swap]
    exact this r w v ⟨hadj.1.symm, hadj.2.symm⟩ (hadj.2.resolve_left h)
  · subst h
    apply not_reachable_of_neighborSet_right_eq_empty hadj.1
    ext x
    aesop

lemma isTree_starGraph (r : V) : (starGraph r).IsTree :=
  ⟨connected_starGraph r, isAcyclic_starGraph r⟩

/-- Every non-center vertex of a starGraph has degree one. -/
lemma degree_starGraph_of_ne_center [Fintype V] [DecidableEq V] {r v : V} (h : v ≠ r) :
    (starGraph r).degree v = 1 :=
  degree_eq_one_iff_existsUnique_adj.mpr ⟨r, by simp [h], by grind [starGraph_adj]⟩

/-- The center vertex of a starGraph has degree (card V) - 1. -/
lemma degree_starGraph_center [Fintype V] [DecidableEq V] {r : V} :
    (starGraph r).degree r = Fintype.card V - 1 := by
  simp

@[simp]
theorem maxDegree_starGraph [Fintype V] [DecidableEq V] (r : V) :
    (starGraph r).maxDegree = Fintype.card V - 1 :=
  have : Nonempty V := ⟨r⟩
  degree_le_maxDegree _ r |>.trans_eq' degree_starGraph_center |>.antisymm' <|
    Nat.le_sub_one_of_lt <| maxDegree_lt_card_verts _

/-- An equivalence of vertex types lifts to an isomorphism of star graphs. -/
@[simps toEquiv]
def starGraphIsoOfEquiv [DecidableEq W] (e : V ≃ W) (v : V) (w : W) :
    starGraph v ≃g starGraph w where
  __ := e.trans <| .swap w (e v)
  map_rel_iff' := by grind [starGraph_adj, e.injective]

@[simp]
theorem toEquiv_starGraphIsoOfEquiv [DecidableEq W] (e : V ≃ W) (v : V) (w : W) :
    starGraphIsoOfEquiv e v w = e.trans (.swap w (e v)) :=
  rfl

@[simp]
theorem coe_starGraphIsoOfEquiv [DecidableEq W] (e : V ≃ W) (v : V) (w : W) :
    ⇑(starGraphIsoOfEquiv e v w) = e.trans (.swap w (e v)) :=
  rfl

/-- An embedding between vertex types lifts to an embedding between star graphs. -/
@[simps toEmbedding]
def starGraphEmbeddingOfEmbedding [DecidableEq W] (f : V ↪ W) (v : V) (w : W) :
    starGraph v ↪g starGraph w where
  __ := f.trans <| Equiv.swap w (f v)
  map_rel_iff' := by simp; grind

@[simp]
theorem coe_starGraphEmbeddingOfEmbedding [DecidableEq W] (f : V ↪ W) (v : V) (w : W) :
    ⇑(starGraphEmbeddingOfEmbedding f v w) = f.trans (Equiv.swap w (f v)) :=
  rfl

@[simp]
theorem toEmbedding_starGraphIsoOfEquiv [DecidableEq W] (e : V ≃ W) (v : V) (w : W) :
    (starGraphIsoOfEquiv e v w).toEmbedding = starGraphEmbeddingOfEmbedding e v w :=
  rfl

theorem starGraph_isContained_starGraph {v : V} {w : W} :
    starGraph v ⊑ starGraph w ↔ Nonempty (V ↪ W) := by
  classical
  exact ⟨(⟨·.some.toEmbedding⟩), fun ⟨f⟩ ↦ starGraphEmbeddingOfEmbedding f v w |>.isContained⟩

theorem starGraph_isIndContained_starGraph {v : V} {w : W} :
    starGraph v ⊴ starGraph w ↔ Nonempty (V ↪ W) := by
  classical
  exact ⟨(⟨·.some.toEmbedding⟩), fun ⟨f⟩ ↦ starGraphEmbeddingOfEmbedding f v w |>.isIndContained⟩

/-- There's a copy of the star graph centered at every vertex. -/
@[simps toHom]
def starGraphCopyNeighborSet (v : V) : Copy (starGraph (none : Option (G.neighborSet v))) G where
  toHom.toFun
  | none => v
  | some u => u
  toHom.map_rel' := by grind [starGraph_adj, mem_neighborSet, adj_symm]
  injective' _ := by grind [RelHom.coeFn_mk, notMem_neighborSet_self]

@[simp]
theorem coe_starGraphCopyNeighborSet (v : V) :
    ⇑(G.starGraphCopyNeighborSet v) = (·.map (↑) |>.getD v) := by
  ext u
  cases u <;> rfl

theorem starGraph_fin_degree_add_one_isContained (v : V) [Fintype (G.neighborSet v)] :
    starGraph (0 : Fin (G.degree v + 1)) ⊑ G := by
  let f := (Fintype.equivFinOfCardEq <| G.card_neighborSet_eq_degree v).symm
  refine ⟨⟨Fin.cons v ((↑) ∘ f), fun {a b} ↦ ?_⟩, by simp [Fin.cons_injective_iff, f.injective]⟩
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    grind [starGraph_adj, Fin.cons, mem_neighborSet, adj_symm]

variable {G} in
theorem starGraph_fin_add_one_isContained_iff_le_maxDegree [Nonempty V] [Fintype V]
    [DecidableRel G.Adj] {n : ℕ} : starGraph (0 : Fin (n + 1)) ⊑ G ↔ n ≤ G.maxDegree := by
  refine ⟨fun h ↦ h.maxDegree_mono.trans_eq' <| by simp, fun h ↦ ?_⟩
  have ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  refine .trans ?_ <| G.starGraph_fin_degree_add_one_isContained v
  grw [starGraph_isContained_starGraph, Fin.nonempty_embedding_iff, h, hv]

end SimpleGraph
