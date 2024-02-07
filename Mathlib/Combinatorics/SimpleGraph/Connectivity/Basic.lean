/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.TrailPath

/-!
# Reachability, connectedness and connected components

## Main definitions

* `Reachable` is the relation indicating whether a walk between a given pair of vertices exists
* `Preconnected` and `Connected` are predicates on simple graphs for pairwise reachability;
  the latter also requires a nonempty vertex type
* `ConnectedComponent` is the type of connected components of a given graph
-/

open Function

namespace SimpleGraph

variable {V V' V'' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')
  {u v w : V}

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
#align simple_graph.reachable SimpleGraph.Reachable

variable {G}

theorem reachable_iff_nonempty_univ :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty
#align simple_graph.reachable_iff_nonempty_univ SimpleGraph.reachable_iff_nonempty_univ

protected theorem Reachable.elim {p : Prop} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp
#align simple_graph.reachable.elim SimpleGraph.Reachable.elim

protected theorem Reachable.elim_path {p : Prop} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath
#align simple_graph.reachable.elim_path SimpleGraph.Reachable.elim_path

protected theorem Walk.reachable {G : SimpleGraph V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩
#align simple_graph.walk.reachable SimpleGraph.Walk.reachable

protected theorem Adj.reachable (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable
#align simple_graph.adj.reachable SimpleGraph.Adj.reachable

@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩
#align simple_graph.reachable.refl SimpleGraph.Reachable.refl

protected theorem Reachable.rfl : G.Reachable u u := Reachable.refl _
#align simple_graph.reachable.rfl SimpleGraph.Reachable.rfl

@[symm]
protected theorem Reachable.symm (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩
#align simple_graph.reachable.symm SimpleGraph.Reachable.symm

theorem reachable_comm : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩
#align simple_graph.reachable_comm SimpleGraph.reachable_comm

@[trans]
protected theorem Reachable.trans (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
#align simple_graph.reachable.trans SimpleGraph.Reachable.trans

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
#align simple_graph.reachable_iff_refl_trans_gen SimpleGraph.reachable_iff_reflTransGen

protected theorem Reachable.map {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩
#align simple_graph.reachable.map SimpleGraph.Reachable.map

@[mono]
protected lemma Reachable.mono {G G' : SimpleGraph V} (h : G ≤ G') (Guv : G.Reachable u v) :
    G'.Reachable u v := Guv.map (SimpleGraph.Hom.mapSpanningSubgraphs h)

theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩
#align simple_graph.iso.reachable_iff SimpleGraph.Iso.reachable_iff

theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]
#align simple_graph.iso.symm_apply_reachable SimpleGraph.Iso.symm_apply_reachable

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)
#align simple_graph.reachable_is_equivalence SimpleGraph.reachable_is_equivalence

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence
#align simple_graph.reachable_setoid SimpleGraph.reachableSetoid

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
#align simple_graph.preconnected SimpleGraph.Preconnected

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _
#align simple_graph.preconnected.map SimpleGraph.Preconnected.map

@[mono]
protected lemma Preconnected.mono {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

lemma top_preconnected : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩
#align simple_graph.iso.preconnected_iff SimpleGraph.Iso.preconnected_iff

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
#align simple_graph.connected SimpleGraph.Connected

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
#align simple_graph.connected.map SimpleGraph.Connected.map

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
#align simple_graph.iso.connected_iff SimpleGraph.Iso.connected_iff

/-- The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent := Quot G.Reachable
#align simple_graph.connected_component SimpleGraph.ConnectedComponent

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v
#align simple_graph.connected_component_mk SimpleGraph.connectedComponentMk

variable {G G'}

namespace ConnectedComponent

@[simps]
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩
#align simple_graph.connected_component.inhabited SimpleGraph.ConnectedComponent.inhabited

@[elab_as_elim]
protected theorem ind {β : G.ConnectedComponent → Prop}
    (h : ∀ v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c
#align simple_graph.connected_component.ind SimpleGraph.ConnectedComponent.ind

@[elab_as_elim]
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h
#align simple_graph.connected_component.ind₂ SimpleGraph.ConnectedComponent.ind₂

protected theorem sound :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound
#align simple_graph.connected_component.sound SimpleGraph.ConnectedComponent.sound

protected theorem exact :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _
#align simple_graph.connected_component.exact SimpleGraph.ConnectedComponent.exact

@[simp]
protected theorem eq :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _
#align simple_graph.connected_component.eq SimpleGraph.ConnectedComponent.eq

theorem connectedComponentMk_eq_of_adj (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable
#align simple_graph.connected_component.connected_component_mk_eq_of_adj SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2
#align simple_graph.connected_component.lift SimpleGraph.ConnectedComponent.lift

@[simp]
protected theorem lift_mk {β : Sort*} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl
#align simple_graph.connected_component.lift_mk SimpleGraph.ConnectedComponent.lift_mk

protected theorem «exists» {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).exists
#align simple_graph.connected_component.exists SimpleGraph.ConnectedComponent.exists

protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).forall
#align simple_graph.connected_component.forall SimpleGraph.ConnectedComponent.forall

theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩
#align simple_graph.preconnected.subsingleton_connected_component SimpleGraph.Preconnected.subsingleton_connectedComponent

/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable
#align simple_graph.connected_component.map SimpleGraph.ConnectedComponent.map

@[simp]
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl
#align simple_graph.connected_component.map_mk SimpleGraph.ConnectedComponent.map_mk

@[simp]
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := by
  refine' C.ind _
  exact fun _ => rfl
#align simple_graph.connected_component.map_id SimpleGraph.ConnectedComponent.map_id

@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) := by
  refine' C.ind _
  exact fun _ => rfl
#align simple_graph.connected_component.map_comp SimpleGraph.ConnectedComponent.map_comp

variable {φ : G ≃g G'} {v' : V'}

@[simp]
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine' C.ind fun u => _
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]
#align simple_graph.connected_component.iso_image_comp_eq_map_iff_eq_comp SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp

@[simp]
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine' C.ind fun u => _
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]
#align simple_graph.connected_component.iso_inv_image_comp_eq_iff_eq_map SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map

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
#align simple_graph.iso.connected_component_equiv SimpleGraph.Iso.connectedComponentEquiv

@[simp]
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl
#align simple_graph.iso.connected_component_equiv_refl SimpleGraph.Iso.connectedComponentEquiv_refl

@[simp]
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_symm SimpleGraph.Iso.connectedComponentEquiv_symm

@[simp]
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_trans SimpleGraph.Iso.connectedComponentEquiv_trans

end Iso

namespace ConnectedComponent

/-- The set of vertices in a connected component of a graph. -/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }
#align simple_graph.connected_component.supp SimpleGraph.ConnectedComponent.supp

@[ext]
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) := by
  refine' ConnectedComponent.ind₂ _
  intro v w
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq]
  intro h
  rw [reachable_comm, h]
#align simple_graph.connected_component.supp_injective SimpleGraph.ConnectedComponent.supp_injective

@[simp]
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff
#align simple_graph.connected_component.supp_inj SimpleGraph.ConnectedComponent.supp_inj

instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective' := ConnectedComponent.supp_injective

@[simp]
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl
#align simple_graph.connected_component.mem_supp_iff SimpleGraph.ConnectedComponent.mem_supp_iff

theorem connectedComponentMk_mem : v ∈ G.connectedComponentMk v :=
  rfl
#align simple_graph.connected_component.connected_component_mk_mem SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext_val (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext_val (φ.toEquiv.right_inv ↑v)
#align simple_graph.connected_component.iso_equiv_supp SimpleGraph.ConnectedComponent.isoEquivSupp

end ConnectedComponent

theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v
#align simple_graph.preconnected.set_univ_walk_nonempty SimpleGraph.Preconnected.set_univ_walk_nonempty

theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v
#align simple_graph.connected.set_univ_walk_nonempty SimpleGraph.Connected.set_univ_walk_nonempty

section Finite

variable (G) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [Walk.mem_finsetWalkLength_iff_length_eq]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩
#align simple_graph.reachable_iff_exists_finset_walk_length_nonempty SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty

instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

instance : Fintype G.ConnectedComponent :=
  @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance : Decidable G.Preconnected :=
  inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)

instance : Decidable G.Connected := by
  rw [connected_iff, ← Finset.univ_nonempty_iff]
  infer_instance

end Finite

end SimpleGraph
