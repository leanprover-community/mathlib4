/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Rémi Bottinelli, Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Mapping walks between graphs

Functions that map walks between different graphs.

## Main definitions

* `SimpleGraph.Walk.map`: The map on walks induced by a graph homomorphism
* `SimpleGraph.Walk.mapLe`: Map a walk to a supergraph
* `SimpleGraph.Walk.transfer`: Map a walk to another graph that contains its edges
* `SimpleGraph.Walk.induce`:
  Map a walk that's fully contained in a set of vertices to the subgraph induced by that set
* `SimpleGraph.Walk.toDeleteEdges`:
  Map a walk that avoids a set of edges to the subgraph with those edges deleted
* `SimpleGraph.Walk.toDeleteEdge`:
  Map a walk that avoids an edge to the subgraph with that edge deleted

## Tags
walks
-/

@[expose] public section

open GraphLike SimpleGraph SymmDartLike

namespace GraphLike.Walk

universe u v w
variable {V : Type u} {V' : Type v} {V'' : Type w}
variable {G : SimpleGraph V} {G' : SimpleGraph V'} {G'' : SimpleGraph V''}

/-! ### Mapping walks -/

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') {u v : V} : Walk G u v → Walk G' (f u) (f v)
  | nil => nil
  | cons s p => cons (f.mapStep s) (p.map f)

variable (f : G →g G') (f' : G' →g G'') {u v u' v' w : V} (p : Walk G u v)

@[simp]
theorem map_nil : (nil : Walk G u u).map f = nil := rfl

@[simp]
theorem map_cons {w : V} (s : step G w u) : (cons s p).map f = cons (f.mapStep s) (p.map f) := rfl

@[simp]
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl) := by
  subst_vars
  rfl

@[simp]
theorem map_id (p : Walk G u v) : p.map Hom.id = p := by
  induction p <;> simp [*]

@[simp]
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by
  induction p <;> simp [*]

/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
work with equality of graph homomorphisms is a necessary evil. -/
theorem map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
    p.map f = (p.map f').copy (h ▸ rfl) (h ▸ rfl) := by
  subst_vars
  rfl

@[simp]
theorem map_eq_nil_iff {p : Walk G u u} : p.map f = nil ↔ p = nil := by cases p <;> simp

@[simp]
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]

theorem map_append {u v w : V} (p : Walk G u v) (q : Walk G v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]

@[simp]
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by
  induction p <;> simp [map_append, *]

@[simp]
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]

@[simp]
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]

@[simp]
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p <;> simp [*]

@[simp]
theorem edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet := by ext; simp

@[simp]
theorem getVert_map (n : ℕ) : (p.map f).getVert n = f (p.getVert n) := by
  induction p generalizing n <;> cases n <;> simp [*]

theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : Walk G u v → Walk G' (f u) (f v)) := by
  intro p p' h
  induction p with
  | nil => cases p' <;> simp at h ⊢
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      grind [Hom.mapStep_injective]

section mapLe

variable {G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : Walk G u v)

/-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
abbrev mapLe : Walk G' u v :=
  p.map (.ofLE h)

set_option backward.isDefEq.respectTransparency false in
lemma support_mapLe_eq_support : (p.mapLe h).support = p.support := by simp

set_option backward.isDefEq.respectTransparency false in
lemma edges_mapLe_eq_edges : (p.mapLe h).edges = p.edges := by simp

set_option backward.isDefEq.respectTransparency false in
lemma edgeSet_mapLe_eq_edgeSet : (p.mapLe h).edgeSet = p.edgeSet := by simp

end mapLe

/-! ### Transferring between graphs -/

/-- Convert a step in a graph to a step in a subgraph. -/
protected def _root_.GraphLike.step.transfer (s : step G u v) (H : SimpleGraph V)
    (h : s(u, v) ∈ H.edgeSet) : step H u v :=
  ⟨s.val, by simpa using h, s.prop.2.1, s.prop.2.2⟩

@[simp]
lemma step.transfer_inv (s : step G u v) (H : SimpleGraph V) (h : s(u, v) ∈ H.edgeSet) :
    (s.transfer H h).inv = s.inv.transfer H (Sym2.eq_swap ▸ h) := by simp

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
-- @[simp]
protected def transfer {u v : V} (p : Walk G u v)
    (H : SimpleGraph V) (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) : Walk H u v :=
  match p with
  | nil => nil
  | cons' u v w s p =>
    cons (s.transfer H (h _ (by simp))) (p.transfer H fun e he => h e (by simp [he]))

theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*, Walk.transfer]

variable {H : SimpleGraph V}

theorem transfer_eq_map_ofLE (hp) (GH : G ≤ H) : p.transfer H hp = p.map (.ofLE GH) := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem edgeSet_transfer (hp) : (p.transfer H hp).edgeSet = p.edgeSet := by ext; simp

@[simp]
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem transfer_transfer (hp) {K : SimpleGraph V} (hp') :
    (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp') := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem transfer_append {w : V} (q : Walk G v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p <;> simp [*, Walk.transfer]

@[simp]
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p <;> simp [*, Walk.transfer]

/-! ### Inducing a walk -/

variable {s s' : Set V}

variable (s) in
/-- A walk in `G` which is fully contained in a set `s` of vertices lifts to a walk of `G[s]`. -/
protected def induce {u v : V} :
    ∀ (w : Walk G u v) (hw : ∀ x ∈ w.support, x ∈ s),
      Walk (G.induce s) ⟨u, hw _ w.start_mem_support⟩ ⟨v, hw _ w.end_mem_support⟩
  | nil, hw => nil
  | cons (v := u') huu' w, hw => .cons (stepInduce _ huu') <| w.induce <| by simp_all

@[simp] lemma induce_nil (hw) : (.nil : Walk G u u).induce s hw = .nil := rfl

@[simp] lemma induce_cons (huu' : step G u u') (w : Walk G u' v) (hw) :
    (w.cons huu').induce s hw = .cons (stepInduce _ huu') (w.induce s <| by simp_all) := rfl

@[simp] lemma support_induce {u v : V} :
    ∀ (w : Walk G u v) (hw), (w.induce s hw).support = w.support.attachWith _ hw
  | .nil, hw => rfl
  | .cons (v := u') hu w, hw => by simp [support_induce]

@[simp] lemma mapStep_induce {u u' : s} (huu' : step G u.val u') :
    (Embedding.induce s).toHom.mapStep (G.stepInduce huu') = huu' := by
  simp [Hom.mapStep]

@[simp] lemma map_induce {u v : V} :
    ∀ (w : Walk G u v) (hw), (w.induce s hw).map (Embedding.induce _).toHom = w
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce]

@[simp] lemma mapStep_induceOfLE {u u' : s} (huu' : step G u.val u') (hs : s ⊆ s') :
    (G.induceHomOfLE hs).toHom.mapStep (G.stepInduce huu') = G.stepInduce (s := s') huu' := by
  simp only [RelHom.coeFn_mk, Function.Embedding.toFun_eq_coe, RelEmbedding.coe_toEmbedding,
    induceHomOfLE_apply, Hom.mapStep, src_eq, tgt_eq, induceHomOfLE_toHom, coe_induceHom,
    Hom.coe_id, val_step_eq, Prod.map_apply, step.ext_iff, Prod.mk.injEq]
  exact Prod.mk_inj.mp rfl

lemma map_induce_induceHomOfLE (hs : s ⊆ s') {u v : V} : ∀ (w : Walk G u v) (hw),
    (w.induce s hw).map (G.induceHomOfLE hs).toHom = w.induce s' (subset_trans hw hs)
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce_induceHomOfLE]

/-! ## Deleting edges -/

/-- Convert a step in a graph to a step in a graph with edges deleted. -/
abbrev _root_.GraphLike.step.toDeleteEdges (s : Set (Sym2 V)) (h : step G u v) (hp : s(u, v) ∉ s) :
    step (G.deleteEdges s) u v :=
  ⟨h.val, deleteEdges_adj.mpr ⟨h.prop.1, by simpa⟩, h.prop.2.1, h.prop.2.2⟩

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
abbrev toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : Walk G v w)
    (hp : ∀ e, e ∈ p.edges → e ∉ s) : Walk (G.deleteEdges s) v w :=
  p.transfer _ <| by
    simp only [edgeSet_deleteEdges, Set.mem_diff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : Walk G v v).toDeleteEdges s hp = Walk.nil := rfl

@[simp]
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : step G u v) (p : Walk G v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons (h.toDeleteEdges s (hp s(u, v) (by simp)))
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `SimpleGraph.Walk.toDeleteEdges`. -/
abbrev toDeleteEdge (e : Sym2 V) (p : Walk G v w) (hp : e ∉ p.edges) :
    Walk (G.deleteEdges {e}) v w :=
  p.toDeleteEdges {e} (fun _ => by contrapose!; simp +contextual [hp])

@[simp]
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : Walk G v w} (hp) :
    Walk.map (.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_ofLE, transfer_transfer, transfer_self]
  apply edges_transfer _ _ ▸ p.edges_subset_edgeSet

end GraphLike.Walk
