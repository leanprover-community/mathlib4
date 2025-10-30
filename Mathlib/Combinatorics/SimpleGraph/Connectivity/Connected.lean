/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
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

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
trails, paths, cycles, bridge edges
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

@[simp] protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _

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
    (h : G ≤ G') (Guv : G.Reachable u v) : G'.Reachable u v := Guv.map (.ofLE h)

theorem Reachable.exists_isPath {u v} (hr : G.Reachable u v) : ∃ p : G.Walk u v, p.IsPath := by
  classical
  obtain ⟨W⟩ := hr
  exact ⟨_, Path.isPath W.toPath⟩

theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩

theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]

lemma Reachable.mem_subgraphVerts {u v} {H : G.Subgraph} (hr : G.Reachable u v)
    (h : ∀ v ∈ H.verts, ∀ w, G.Adj v w → H.Adj v w)
    (hu : u ∈ H.verts) : v ∈ H.verts := by
  let rec aux {v' : V} (hv' : v' ∈ H.verts) (p : G.Walk v' v) : v ∈ H.verts := by
    by_cases hnp : p.Nil
    · exact hnp.eq ▸ hv'
    exact aux (H.edge_vert (h _ hv' _ (Walk.adj_snd hnp)).symm) p.tail
  termination_by p.length
  decreasing_by {
    rw [← Walk.length_tail_add_one hnp]
    omega
  }
  exact aux hu hr.some

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)

/-- Distinct vertices are not reachable in the empty graph. -/
@[simp]
lemma reachable_bot {u v : V} : (⊥ : SimpleGraph V).Reachable u v ↔ u = v :=
  ⟨fun h ↦ h.elim fun p ↦ match p with | .nil => rfl, fun h ↦ h ▸ .rfl⟩

@[simp] lemma reachable_top {u v : V} : (completeGraph V).Reachable u v := by
  obtain rfl | huv := eq_or_ne u v
  · simp
  · exact ⟨.cons huv .nil⟩

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _

@[mono]
protected lemma Preconnected.mono {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

lemma preconnected_bot_iff_subsingleton : (⊥ : SimpleGraph V).Preconnected ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa [subsingleton_iff, ← reachable_bot] using h⟩
  contrapose! h
  simp [nontrivial_iff.mp h, Preconnected, reachable_bot]

lemma preconnected_bot [Subsingleton V] : (⊥ : SimpleGraph V).Preconnected :=
  preconnected_bot_iff_subsingleton.mpr ‹_›

lemma not_preconnected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Preconnected :=
  preconnected_bot_iff_subsingleton.not.mpr <| not_subsingleton_iff_nontrivial.mpr ‹_›

@[simp] lemma preconnected_top : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

@[deprecated (since := "2025-09-23")] alias bot_preconnected := preconnected_bot
@[deprecated (since := "2025-09-23")]
alias bot_preconnected_iff_subsingleton := preconnected_bot_iff_subsingleton
@[deprecated (since := "2025-09-23")] alias bot_not_preconnected := not_preconnected_bot
@[deprecated (since := "2025-09-23")] alias top_preconnected := preconnected_top

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩

lemma Preconnected.support_eq_univ [Nontrivial V] {G : SimpleGraph V}
    (h : G.Preconnected) : G.support = Set.univ := by
  simp only [Set.eq_univ_iff_forall]
  intro v
  obtain ⟨w, hw⟩ := exists_ne v
  obtain ⟨p⟩ := h v w
  cases p with
  | nil => contradiction
  | @cons _ w => exact ⟨w, ‹_›⟩

lemma Preconnected.degree_pos_of_nontrivial [Nontrivial V] {G : SimpleGraph V} (h : G.Preconnected)
    (v : V) [Fintype (G.neighborSet v)] : 0 < G.degree v := by
  simp [degree_pos_iff_mem_support, h.support_eq_univ]

lemma Preconnected.minDegree_pos_of_nontrivial [Nontrivial V] [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (h : G.Preconnected) : 0 < G.minDegree := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  exact h.degree_pos_of_nontrivial v

lemma adj_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil) {x : V}
    (hx : x ∈ p.support) : ∃ y ∈ p.support, G.Adj x y := by
  induction p with
  | nil =>
    exact (hp Walk.Nil.nil).elim
  | @cons u v w h p ih =>
    cases List.mem_cons.mp hx with
    | inl hxu =>
      rw [hxu]
      exact ⟨v, ⟨((Walk.cons h p).mem_support_iff).mpr (Or.inr p.start_mem_support), h⟩⟩
    | inr hxp =>
      cases Decidable.em p.Nil with
      | inl hnil =>
        rw [Walk.nil_iff_support_eq.mp hnil] at hxp
        rw [show (x = v) by simp_all]
        exact ⟨u, ⟨(Walk.cons h p).start_mem_support, G.adj_symm h⟩⟩
      | inr hnotnil =>
        obtain ⟨y, hy⟩ := ih hnotnil hxp
        refine ⟨y, ⟨?_, hy.right⟩⟩
        rw [Walk.mem_support_iff]
        simp only [Walk.support_cons, List.tail_cons]
        exact Or.inr hy.left

lemma mem_support_of_mem_walk_support {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : ¬p.Nil)
    {w : V} (hw : w ∈ p.support) : w ∈ G.support := by
  obtain ⟨y, hy⟩ := adj_of_mem_walk_support p hp hw
  exact (mem_support G).mpr ⟨y, hy.right⟩

lemma mem_support_of_reachable {G : SimpleGraph V} {u v : V} (huv : u ≠ v) (h : G.Reachable u v) :
    u ∈ G.support := by
  let p : G.Walk u v := Classical.choice h
  have hp : ¬p.Nil := Walk.not_nil_of_ne huv
  exact mem_support_of_mem_walk_support p hp p.start_mem_support

theorem Preconnected.exists_isPath {G : SimpleGraph V} (h : G.Preconnected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

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

theorem Connected.exists_isPath {G : SimpleGraph V} (h : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath :=
  (h u v).exists_isPath

lemma connected_bot_iff : (⊥ : SimpleGraph V).Connected ↔ Subsingleton V ∧ Nonempty V := by
  simp [preconnected_bot_iff_subsingleton, connected_iff]

lemma not_connected_bot [Nontrivial V] : ¬(⊥ : SimpleGraph V).Connected := by
  simp [not_preconnected_bot, connected_iff]

lemma connected_top_iff : (completeGraph V).Connected ↔ Nonempty V := by simp [connected_iff]

@[simp] lemma connected_top [Nonempty V] : (completeGraph V).Connected := by rwa [connected_top_iff]

@[deprecated (since := "2025-09-23")] alias bot_not_connected := not_connected_bot
@[deprecated (since := "2025-09-23")] alias top_connected := connected_top

theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩

theorem connected_or_connected_compl [Nonempty V] : G.Connected ∨ Gᶜ.Connected := by
  have ⟨v₀⟩ := ‹Nonempty V›
  by_cases hreach₀ : ∀ v, G.Reachable v₀ v
  · exact .inl <| G.connected_iff_exists_forall_reachable.mpr ⟨v₀, hreach₀⟩
  refine .inr <| Gᶜ.connected_iff_exists_forall_reachable.mpr ⟨v₀, fun v ↦ ?_⟩
  have ⟨v₁, hreach₁⟩ := not_forall.mp hreach₀
  have hcadj₁ : Gᶜ.Adj v₀ v₁ :=
    ⟨fun heq ↦ heq ▸ hreach₁ <| Reachable.refl _, mt Adj.reachable hreach₁⟩
  by_cases hreach : G.Reachable v₀ v
  · by_cases heq : v = v₁
    · exact heq ▸ hcadj₁.reachable
    have : Gᶜ.Adj v v₁ := ⟨heq, fun hadj ↦ hreach₁ <| hreach.trans hadj.reachable⟩
    exact hcadj₁.reachable.trans this.reachable.symm
  by_cases heq : v₀ = v
  · exact heq ▸ .refl _
  exact Adj.reachable ⟨heq, mt Adj.reachable hreach⟩

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

instance isEmpty [IsEmpty V] : IsEmpty (ConnectedComponent G) := by
  by_contra! hc
  obtain ⟨v, _⟩ := hc.some.exists_rep
  exact IsEmpty.false v

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
  Quot.mk_surjective.exists

protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  Quot.mk_surjective.forall

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
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := C.ind (fun _ => rfl)

@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) :=
  C.ind (fun _ => rfl)

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
  left_inv C := C.ind (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v))
  right_inv C := C.ind (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v))

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
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq]
  intro v w h
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

lemma mem_supp_congr_adj {v w : V} (c : G.ConnectedComponent) (hadj : G.Adj v w) :
    v ∈ c.supp ↔ w ∈ c.supp := by
  simp only [ConnectedComponent.mem_supp_iff] at *
  constructor <;> intro h <;> simp only [← h] <;> apply connectedComponentMk_eq_of_adj
  · exact hadj.symm
  · exact hadj

theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl

theorem nonempty_supp (C : G.ConnectedComponent) : C.supp.Nonempty := C.exists_rep

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext (φ.toEquiv.right_inv ↑v)

lemma mem_coe_supp_of_adj {v w : V} {H : Subgraph G} {c : ConnectedComponent H.coe}
    (hv : v ∈ (↑) '' (c : Set H.verts)) (hw : w ∈ H.verts)
    (hadj : H.Adj v w) : w ∈ (↑) '' (c : Set H.verts) := by
  obtain ⟨_, h⟩ := hv
  use ⟨w, hw⟩
  rw [← (mem_supp_iff _ _).mp h.1]
  exact ⟨connectedComponentMk_eq_of_adj <| Subgraph.Adj.coe <| h.2 ▸ hadj.symm, rfl⟩

lemma eq_of_common_vertex {v : V} {c c' : ConnectedComponent G} (hc : v ∈ c.supp)
    (hc' : v ∈ c'.supp) : c = c' := by
  simp only [mem_supp_iff] at *
  rw [← hc, ← hc']

lemma connectedComponentMk_supp_subset_supp {G'} {v : V} (h : G ≤ G') (c' : G'.ConnectedComponent)
    (hc' : v ∈ c'.supp) : (G.connectedComponentMk v).supp ⊆ c'.supp := by
  intro v' hv'
  simp only [mem_supp_iff, ConnectedComponent.eq] at hv' ⊢
  rw [ConnectedComponent.sound (hv'.mono h)]
  exact hc'

lemma biUnion_supp_eq_supp {G G' : SimpleGraph V} (h : G ≤ G') (c' : ConnectedComponent G') :
    ⋃ (c : ConnectedComponent G) (_ : c.supp ⊆ c'.supp), c.supp = c'.supp := by
  ext v
  simp_rw [Set.mem_iUnion]
  refine ⟨fun ⟨_, ⟨hi, hi'⟩⟩ ↦ hi hi', ?_⟩
  intro hv
  use G.connectedComponentMk v
  use c'.connectedComponentMk_supp_subset_supp h hv
  simp only [mem_supp_iff]

lemma top_supp_eq_univ (c : ConnectedComponent (⊤ : SimpleGraph V)) :
    c.supp = (Set.univ : Set V) := by
  obtain ⟨w, rfl⟩ := c.exists_rep
  ext v
  simpa [-ConnectedComponent.eq] using ConnectedComponent.sound (G := ⊤)

lemma reachable_of_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hv : v ∈ C.supp) : G.Reachable u v := by
  rw [mem_supp_iff] at hu hv
  exact ConnectedComponent.exact (hv ▸ hu)

lemma mem_supp_of_adj_mem_supp {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C.supp) (hadj : G.Adj u v) : v ∈ C.supp := (mem_supp_congr_adj C hadj).mp hu

/--
Given a connected component `C` of a simple graph `G`, produce the induced graph on `C`.
The declaration `connected_toSimpleGraph` shows it is connected, and `toSimpleGraph_hom`
provides the homomorphism back to `G`.
-/
def toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) : SimpleGraph C := G.induce C.supp

/-- Homomorphism from a connected component graph to the original graph. -/
def toSimpleGraph_hom {G : SimpleGraph V} (C : G.ConnectedComponent) : C.toSimpleGraph →g G where
  toFun u := u.val
  map_rel' := id

lemma toSimpleGraph_hom_apply {G : SimpleGraph V} (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph_hom u = u.val := rfl

lemma toSimpleGraph_adj {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V} (hu : u ∈ C)
    (hv : v ∈ C) : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨v, hv⟩ ↔ G.Adj u v := by
  simp [toSimpleGraph]

lemma adj_spanningCoe_toSimpleGraph {v w : V} (C : G.ConnectedComponent) :
    C.toSimpleGraph.spanningCoe.Adj v w ↔ v ∈ C.supp ∧ G.Adj v w := by
  apply Iff.intro
  · intro h
    simp_all only [map_adj, SetLike.coe_sort_coe, Subtype.exists, mem_supp_iff]
    obtain ⟨_, a, _, _, h₁, h₂, h₃⟩ := h
    subst h₂ h₃
    exact ⟨a, h₁⟩
  · simp only [toSimpleGraph, map_adj, comap_adj, Embedding.subtype_apply, Subtype.exists,
      exists_and_left, and_imp]
    intro h hadj
    exact ⟨v, h, w, hadj, rfl, (C.mem_supp_congr_adj hadj).mp h, rfl⟩

@[deprecated (since := "2025-05-08")]
alias adj_spanningCoe_induce_supp := adj_spanningCoe_toSimpleGraph

/-- Get the walk between two vertices in a connected component from a walk in the original graph. -/
private def walk_toSimpleGraph' {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) (p : G.Walk u v) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ := by
  cases p with
  | nil => exact Walk.nil
  | @cons v w u h p =>
    have hw : w ∈ C := C.mem_supp_of_adj_mem_supp hu h
    have h' : C.toSimpleGraph.Adj ⟨u, hu⟩ ⟨w, hw⟩ := h
    exact Walk.cons h' (C.walk_toSimpleGraph' hw hv p)

@[deprecated (since := "2025-05-08")] alias reachable_induce_supp := walk_toSimpleGraph'

/-- There is a walk between every pair of vertices in a connected component. -/
noncomputable def walk_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C.toSimpleGraph.Walk ⟨u, hu⟩ ⟨v, hv⟩ :=
  C.walk_toSimpleGraph' hu hv (C.reachable_of_mem_supp hu hv).some

lemma reachable_toSimpleGraph {G : SimpleGraph V} (C : G.ConnectedComponent) {u v : V}
    (hu : u ∈ C) (hv : v ∈ C) : C.toSimpleGraph.Reachable ⟨u, hu⟩ ⟨v, hv⟩ :=
  Walk.reachable (C.walk_toSimpleGraph hu hv)

lemma connected_toSimpleGraph (C : ConnectedComponent G) : (C.toSimpleGraph).Connected where
  preconnected := by
    intro ⟨u, hu⟩ ⟨v, hv⟩
    exact C.reachable_toSimpleGraph hu hv
  nonempty := ⟨C.out, C.out_eq⟩

@[deprecated (since := "2025-05-08")] alias connected_induce_supp := connected_toSimpleGraph

end ConnectedComponent

/-- Given graph homomorphisms from each connected component of `G` to `H` this is the graph
homomorphism from `G` to `H` -/
@[simps]
def homOfConnectedComponents (G : SimpleGraph V) {H : SimpleGraph V'}
    (C : (c : G.ConnectedComponent) → c.toSimpleGraph →g H) : G →g H where
  toFun := fun x ↦ (C (G.connectedComponentMk _)) _
  map_rel' := fun hab ↦ by
    have h : (G.connectedComponentMk _).toSimpleGraph.Adj ⟨_, rfl⟩
        ⟨_, ((G.connectedComponentMk _).mem_supp_congr_adj hab).1 rfl⟩ := by simpa using hab
    convert (C (G.connectedComponentMk _)).map_rel h using 3 <;>
      rw [ConnectedComponent.connectedComponentMk_eq_of_adj hab]

-- TODO: Extract as lemma about general equivalence relation
lemma pairwise_disjoint_supp_connectedComponent (G : SimpleGraph V) :
    Pairwise fun c c' : ConnectedComponent G ↦ Disjoint c.supp c'.supp := by
  simp_rw [Set.disjoint_left]
  intro _ _ h a hsx hsy
  rw [ConnectedComponent.mem_supp_iff] at hsx hsy
  rw [hsx] at hsy
  exact h hsy

-- TODO: Extract as lemma about general equivalence relation
lemma iUnion_connectedComponentSupp (G : SimpleGraph V) :
    ⋃ c : G.ConnectedComponent, c.supp = Set.univ := by
  refine Set.eq_univ_of_forall fun v ↦ ⟨G.connectedComponentMk v, ?_⟩
  simp only [Set.mem_range, SetLike.mem_coe]
  exact ⟨⟨G.connectedComponentMk v, rfl⟩, rfl⟩

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

theorem reachable_delete_edges_iff_exists_walk {v w v' w' : V} :
    (G \ fromEdgeSet {s(v, w)}).Reachable v' w' ↔ ∃ p : G.Walk v' w', s(v, w) ∉ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (.ofLE (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.ofLE_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag]
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
    · simp only [Sym2.eq_swap, Walk.edges_cons, List.mem_cons, true_or]
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

theorem isBridge_iff_adj_and_forall_cycle_notMem {v w : V} : G.IsBridge s(v, w) ↔
    G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges := by
  rw [isBridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and]

@[deprecated (since := "2025-05-23")]
alias isBridge_iff_adj_and_forall_cycle_not_mem := isBridge_iff_adj_and_forall_cycle_notMem

theorem isBridge_iff_mem_and_forall_cycle_notMem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun _ _ => isBridge_iff_adj_and_forall_cycle_notMem) e

@[deprecated (since := "2025-05-23")]
alias isBridge_iff_mem_and_forall_cycle_not_mem := isBridge_iff_mem_and_forall_cycle_notMem

/-- Deleting a non-bridge edge from a connected graph preserves connectedness. -/
lemma Connected.connected_delete_edge_of_not_isBridge (hG : G.Connected) {x y : V}
    (h : ¬ G.IsBridge s(x, y)) : (G.deleteEdges {s(x, y)}).Connected := by
  classical
  simp only [isBridge_iff, not_and, not_not] at h
  obtain hxy | hxy := em' <| G.Adj x y
  · rwa [deleteEdges, Disjoint.sdiff_eq_left (by simpa)]
  refine (connected_iff_exists_forall_reachable _).2 ⟨x, fun w ↦ ?_⟩
  obtain ⟨P, hP⟩ := hG.exists_isPath w x
  obtain heP | heP := em' <| s(x, y) ∈ P.edges
  · exact ⟨(P.toDeleteEdges {s(x, y)} (by aesop)).reverse⟩
  have hyP := P.snd_mem_support_of_mem_edges heP
  let P₁ := P.takeUntil y hyP
  have hxP₁ := Walk.endpoint_notMem_support_takeUntil hP hyP hxy.ne
  have heP₁ : s(x, y) ∉ P₁.edges := fun h ↦ hxP₁ <| P₁.fst_mem_support_of_mem_edges h
  exact (h hxy).trans (Reachable.symm ⟨P₁.toDeleteEdges {s(x, y)} (by aesop)⟩)

end BridgeEdges

end SimpleGraph
