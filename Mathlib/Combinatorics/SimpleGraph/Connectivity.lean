/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Subgraph

/-!

## Main definitions

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
bridge edges

-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

variable {G}

theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty

lemma not_reachable_iff_isEmpty_walk {u v : V} : ¬G.Reachable u v ↔ IsEmpty (G.Walk u v) :=
  not_nonempty_iff

protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp

protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath

protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩

protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable

@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩

protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _

@[symm]
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩

theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩

@[trans]
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩

theorem reachable_iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩

protected theorem Reachable.map {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩

@[mono]
protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
    (h : G ≤ G') (Guv : G.Reachable u v) : G'.Reachable u v :=
  Guv.map (SimpleGraph.Hom.mapSpanningSubgraphs h)

theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _

@[mono]
protected lemma Preconnected.mono  {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

lemma top_preconnected : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]

lemma connected_iff_exists_forall_reachable : G.Connected ↔ ∃ v, ∀ w, G.Reachable v w := by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v := ⟨fun h => h.preconnected⟩

theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩

@[mono]
protected lemma Connected.mono {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.Connected) : G'.Connected where
  preconnected := hG.preconnected.mono h
  nonempty := hG.nonempty

lemma top_connected [Nonempty V] : (⊤ : SimpleGraph V).Connected where
  preconnected := top_preconnected

theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

/-- The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent := Quot G.Reachable

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v

variable {G G' G''}

namespace ConnectedComponent

@[simps]
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩

@[elab_as_elim]
protected theorem ind {β : G.ConnectedComponent → Prop}
    (h : ∀ v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c

@[elab_as_elim]
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h

protected theorem sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound

protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _

@[simp]
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _

theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2

@[simp]
protected theorem lift_mk {β : Sort*} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl

protected theorem «exists» {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).exists

protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).forall

theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
def recOn
    {motive : G.ConnectedComponent → Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) → motive (G.connectedComponentMk v))
    (h : ∀ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f fun u v r => r.elim_path fun p => h u v p p.2

/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable

@[simp]
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl

@[simp]
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := by
  refine C.ind ?_
  exact fun _ => rfl

@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) := by
  refine C.ind ?_
  exact fun _ => rfl

variable {φ : G ≃g G'} {v : V} {v' : V'}

@[simp]
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]

@[simp]
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]

end ConnectedComponent

namespace Iso

/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := ConnectedComponent.ind
    (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v)) C
  right_inv C := ConnectedComponent.ind
    (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v)) C

@[simp]
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl

@[simp]
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl

@[simp]
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl

end Iso

namespace ConnectedComponent

/-- The set of vertices in a connected component of a graph. -/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }

@[ext]
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  intro v w
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq]
  intro h
  rw [reachable_comm, h]

@[simp]
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff

instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective' := ConnectedComponent.supp_injective

@[simp]
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl

theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext_val (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext_val (φ.toEquiv.right_inv ↑v)

lemma mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
    (hv : v ∈ (↑) '' (c : Set H.verts)) (hw : w ∈ H.verts)
    (hadj : H.Adj v w) : w ∈ (↑) '' (c : Set H.verts):= by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
  exact ⟨connectedComponentMk_eq_of_adj <| Subgraph.Adj.coe <| h.2 ▸ hadj.symm, rfl⟩

end ConnectedComponent

theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v

theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v

/-! ### Bridge edges -/
section BridgeEdges

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, by simp [reachable_comm]⟩ e

theorem isBridge_iff {u v : V} :
    G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v := Iff.rfl

theorem reachable_delete_edges_iff_exists_walk {v w : V} :
    (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔ ∃ p : G.Walk v w, ¬s(v, w) ∈ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (Hom.mapSpanningSubgraphs (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.mapSpanningSubgraphs_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
      Set.mem_singleton_iff]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩

theorem isBridge_iff_adj_and_forall_walk_mem_edges {v w : V} :
    G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v, w) ∈ p.edges := by
  rw [isBridge_iff, and_congr_right']
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not]

theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : ∀ p : G.Walk v w, s(v, w) ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse, List.mem_reverse] at hpq'
  rw [Walk.isTrail_def, this, Walk.edges_append, Walk.edges_append, List.nodup_append_comm,
    ← List.append_assoc, ← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'

-- Porting note: the unused variable checker helped eliminate a good amount of this proof (!)
theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_delete_edges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset p h)
    · simp only [Sym2.eq_swap, Walk.edges_cons, List.mem_cons, eq_self_iff_true, true_or_iff]
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : ∀ p : G.Walk w v, s(w, v) ∈ p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(Walk.rotate_edges c hvc).mem_iff, Sym2.eq_swap]

theorem isBridge_iff_adj_and_forall_cycle_not_mem {v w : V} : G.IsBridge s(v, w) ↔
    G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges := by
  rw [isBridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and_iff]

theorem isBridge_iff_mem_and_forall_cycle_not_mem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun _ _ => isBridge_iff_adj_and_forall_cycle_not_mem) e

end BridgeEdges

end SimpleGraph
