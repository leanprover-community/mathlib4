/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finite.Set

/-!
# Ends

This file contains a definition of the ends of a simple graph, as sections of the inverse system
assigning, to each finite set of vertices, the connected components of its complement.
-/


universe u

variable {V : Type u} (G : SimpleGraph V) (K L M : Set V)

namespace SimpleGraph

/-- The components outside a given set of vertices `K` -/
abbrev ComponentCompl :=
  (G.induce Kᶜ).ConnectedComponent

variable {G} {K L M}

/-- The connected component of `v` in `G.induce Kᶜ`. -/
abbrev componentComplMk (G : SimpleGraph V) {v : V} (vK : v ∉ K) : G.ComponentCompl K :=
  connectedComponentMk (G.induce Kᶜ) ⟨v, vK⟩

/-- The set of vertices of `G` making up the connected component `C` -/
def ComponentCompl.supp (C : G.ComponentCompl K) : Set V :=
  { v : V | ∃ h : v ∉ K, G.componentComplMk h = C }

@[ext]
theorem ComponentCompl.supp_injective :
    Function.Injective (ComponentCompl.supp : G.ComponentCompl K → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq, ComponentCompl.supp] at h ⊢
  exact ((h v).mp ⟨hv, Reachable.refl _⟩).choose_spec

theorem ComponentCompl.supp_inj {C D : G.ComponentCompl K} : C.supp = D.supp ↔ C = D :=
  ComponentCompl.supp_injective.eq_iff

instance ComponentCompl.setLike : SetLike (G.ComponentCompl K) V where
  coe := ComponentCompl.supp
  coe_injective' _ _ := ComponentCompl.supp_inj.mp

@[simp]
theorem ComponentCompl.mem_supp_iff {v : V} {C : ComponentCompl G K} :
    v ∈ C ↔ ∃ vK : v ∉ K, G.componentComplMk vK = C :=
  Iff.rfl

theorem componentComplMk_mem (G : SimpleGraph V) {v : V} (vK : v ∉ K) : v ∈ G.componentComplMk vK :=
  ⟨vK, rfl⟩

theorem componentComplMk_eq_of_adj (G : SimpleGraph V) {v w : V} (vK : v ∉ K) (wK : w ∉ K)
    (a : G.Adj v w) : G.componentComplMk vK = G.componentComplMk wK := by
  rw [ConnectedComponent.eq]
  apply Adj.reachable
  exact a

/-- In an infinite graph, the set of components out of a finite set is nonempty. -/
instance componentCompl_nonempty_of_infinite (G : SimpleGraph V) [Infinite V] (K : Finset V) :
    Nonempty (G.ComponentCompl K) :=
  let ⟨_, kK⟩ := K.finite_toSet.infinite_compl.nonempty
  ⟨componentComplMk _ kK⟩

namespace ComponentCompl

/-- A `ComponentCompl` specialization of `Quot.lift`, where soundness has to be proved only
for adjacent vertices.
-/
protected def lift {β : Sort*} (f : ∀ ⦃v⦄ (_ : v ∉ K), β)
    (h : ∀ ⦃v w⦄ (hv : v ∉ K) (hw : w ∉ K), G.Adj v w → f hv = f hw) : G.ComponentCompl K → β :=
  ConnectedComponent.lift (fun vv => f vv.prop) fun v w p => by
    induction p with
    | nil => rintro _; rfl
    | cons a q ih => rename_i u v w; rintro h'; exact (h u.prop v.prop a).trans (ih h'.of_cons)

@[elab_as_elim]
protected theorem ind {β : G.ComponentCompl K → Prop}
    (f : ∀ ⦃v⦄ (hv : v ∉ K), β (G.componentComplMk hv)) : ∀ C : G.ComponentCompl K, β C := by
  apply ConnectedComponent.ind
  exact fun ⟨v, vnK⟩ => f vnK

/-- The induced graph on the vertices `C`. -/
protected abbrev coeGraph (C : ComponentCompl G K) : SimpleGraph C :=
  G.induce (C : Set V)

theorem coe_inj {C D : G.ComponentCompl K} : (C : Set V) = (D : Set V) ↔ C = D :=
  SetLike.coe_set_eq

@[simp]
protected theorem nonempty (C : G.ComponentCompl K) : (C : Set V).Nonempty :=
  C.ind fun v vnK => ⟨v, vnK, rfl⟩

protected theorem exists_eq_mk (C : G.ComponentCompl K) :
    ∃ (v : _) (h : v ∉ K), G.componentComplMk h = C :=
  C.nonempty

protected theorem disjoint_right (C : G.ComponentCompl K) : Disjoint K C := by
  rw [Set.disjoint_iff]
  exact fun v ⟨vK, vC⟩ => vC.choose vK

theorem notMem_of_mem {C : G.ComponentCompl K} {c : V} (cC : c ∈ C) : c ∉ K := fun cK =>
  Set.disjoint_iff.mp C.disjoint_right ⟨cK, cC⟩

@[deprecated (since := "2025-05-23")] alias not_mem_of_mem := notMem_of_mem

protected theorem pairwise_disjoint :
    Pairwise fun C D : G.ComponentCompl K => Disjoint (C : Set V) (D : Set V) := by
  rintro C D ne
  rw [Set.disjoint_iff]
  exact fun u ⟨uC, uD⟩ => ne (uC.choose_spec.symm.trans uD.choose_spec)

/-- Any vertex adjacent to a vertex of `C` and not lying in `K` must lie in `C`.
-/
theorem mem_of_adj : ∀ {C : G.ComponentCompl K} (c d : V), c ∈ C → d ∉ K → G.Adj c d → d ∈ C :=
  fun {C} c d ⟨cnK, h⟩ dnK cd =>
  ⟨dnK, by
    rw [← h, ConnectedComponent.eq]
    exact Adj.reachable cd.symm⟩

/--
Assuming `G` is preconnected and `K` not empty, given any connected component `C` outside of `K`,
there exists a vertex `k ∈ K` adjacent to a vertex `v ∈ C`.
-/
theorem exists_adj_boundary_pair (Gc : G.Preconnected) (hK : K.Nonempty) :
    ∀ C : G.ComponentCompl K, ∃ ck : V × V, ck.1 ∈ C ∧ ck.2 ∈ K ∧ G.Adj ck.1 ck.2 := by
  refine ComponentCompl.ind fun v vnK => ?_
  let C : G.ComponentCompl K := G.componentComplMk vnK
  let dis := Set.disjoint_iff.mp C.disjoint_right
  by_contra! h
  suffices Set.univ = (C : Set V) by exact dis ⟨hK.choose_spec, this ▸ Set.mem_univ hK.some⟩
  symm
  rw [Set.eq_univ_iff_forall]
  rintro u
  by_contra unC
  obtain ⟨p⟩ := Gc v u
  obtain ⟨⟨⟨x, y⟩, xy⟩, -, xC, ynC⟩ :=
    p.exists_boundary_dart (C : Set V) (G.componentComplMk_mem vnK) unC
  exact ynC (mem_of_adj x y xC (fun yK : y ∈ K => h ⟨x, y⟩ xC yK xy) xy)

/--
If `K ⊆ L`, the components outside of `L` are all contained in a single component outside of `K`.
-/
abbrev hom (h : K ⊆ L) (C : G.ComponentCompl L) : G.ComponentCompl K :=
  C.map <| induceHom Hom.id <| Set.compl_subset_compl.2 h

theorem subset_hom (C : G.ComponentCompl L) (h : K ⊆ L) : (C : Set V) ⊆ (C.hom h : Set V) := by
  rintro c ⟨cL, rfl⟩
  exact ⟨fun h' => cL (h h'), rfl⟩

theorem _root_.SimpleGraph.componentComplMk_mem_hom
    (G : SimpleGraph V) {v : V} (vK : v ∉ K) (h : L ⊆ K) :
    v ∈ (G.componentComplMk vK).hom h :=
  subset_hom (G.componentComplMk vK) h (G.componentComplMk_mem vK)

theorem hom_eq_iff_le (C : G.ComponentCompl L) (h : K ⊆ L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ (C : Set V) ⊆ (D : Set V) :=
  ⟨fun h' => h' ▸ C.subset_hom h, C.ind fun _ vnL vD => (vD ⟨vnL, rfl⟩).choose_spec⟩

theorem hom_eq_iff_not_disjoint (C : G.ComponentCompl L) (h : K ⊆ L) (D : G.ComponentCompl K) :
    C.hom h = D ↔ ¬Disjoint (C : Set V) (D : Set V) := by
  rw [Set.not_disjoint_iff]
  constructor
  · rintro rfl
    refine C.ind fun x xnL => ?_
    exact ⟨x, ⟨xnL, rfl⟩, ⟨fun xK => xnL (h xK), rfl⟩⟩
  · refine C.ind fun x xnL => ?_
    rintro ⟨x, ⟨_, e₁⟩, _, rfl⟩
    rw [← e₁]
    rfl

theorem hom_refl (C : G.ComponentCompl L) : C.hom (subset_refl L) = C := by
  change C.map _ = C
  rw [induceHom_id G Lᶜ, ConnectedComponent.map_id]

theorem hom_trans (C : G.ComponentCompl L) (h : K ⊆ L) (h' : M ⊆ K) :
    C.hom (h'.trans h) = (C.hom h).hom h' := by
  change C.map _ = (C.map _).map _
  rw [ConnectedComponent.map_comp, induceHom_comp]
  rfl

theorem hom_mk {v : V} (vnL : v ∉ L) (h : K ⊆ L) :
    (G.componentComplMk vnL).hom h = G.componentComplMk (Set.notMem_subset h vnL) :=
  rfl

theorem hom_infinite (C : G.ComponentCompl L) (h : K ⊆ L) (Cinf : (C : Set V).Infinite) :
    (C.hom h : Set V).Infinite :=
  Set.Infinite.mono (C.subset_hom h) Cinf

theorem infinite_iff_in_all_ranges {K : Finset V} (C : G.ComponentCompl K) :
    C.supp.Infinite ↔ ∀ (L) (h : K ⊆ L), ∃ D : G.ComponentCompl L, D.hom h = C := by
  classical
    constructor
    · rintro Cinf L h
      obtain ⟨v, ⟨vK, rfl⟩, vL⟩ := Set.Infinite.nonempty (Set.Infinite.diff Cinf L.finite_toSet)
      exact ⟨componentComplMk _ vL, rfl⟩
    · rintro h Cfin
      obtain ⟨D, e⟩ := h (K ∪ Cfin.toFinset) Finset.subset_union_left
      obtain ⟨v, vD⟩ := D.nonempty
      let Ddis := D.disjoint_right
      simp_rw [Finset.coe_union, Set.Finite.coe_toFinset, Set.disjoint_union_left,
        Set.disjoint_iff] at Ddis
      exact Ddis.right ⟨(ComponentCompl.hom_eq_iff_le _ _ _).mp e vD, vD⟩

end ComponentCompl

/-- For a locally finite preconnected graph, the number of components outside of any finite set
is finite. -/
instance componentCompl_finite [LocallyFinite G] [Gpc : Fact G.Preconnected] (K : Finset V) :
    Finite (G.ComponentCompl K) := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | h
  -- If K is empty, then removing K doesn't change the graph, which is connected, hence has a
  -- single connected component
  · dsimp [ComponentCompl]
    rw [Finset.coe_empty, Set.compl_empty]
    have := Gpc.out.subsingleton_connectedComponent
    exact Finite.of_equiv _ (induceUnivIso G).connectedComponentEquiv.symm
  -- Otherwise, we consider the function `touch` mapping a connected component to one of its
  -- vertices adjacent to `K`.
  · let touch (C : G.ComponentCompl K) : {v : V | ∃ k : V, k ∈ K ∧ G.Adj k v} :=
      let p := C.exists_adj_boundary_pair Gpc.out h
      ⟨p.choose.1, p.choose.2, p.choose_spec.2.1, p.choose_spec.2.2.symm⟩
    -- `touch` is injective
    have touch_inj : touch.Injective := fun C D h' => ComponentCompl.pairwise_disjoint.eq
      (Set.not_disjoint_iff.mpr ⟨touch C, (C.exists_adj_boundary_pair Gpc.out h).choose_spec.1,
                                 h'.symm ▸ (D.exists_adj_boundary_pair Gpc.out h).choose_spec.1⟩)
    -- `touch` has finite range
    have : Finite (Set.range touch) := by
      refine @Subtype.finite _ (Set.Finite.to_subtype ?_) _
      apply Set.Finite.ofFinset (K.biUnion (fun v => G.neighborFinset v))
      simp only [Finset.mem_biUnion, mem_neighborFinset, Set.mem_setOf_eq, implies_true]
    -- hence `touch` has a finite domain
    apply Finite.of_injective_finite_range touch_inj

section Ends

variable (G)

open CategoryTheory

/--
The functor assigning, to a finite set in `V`, the set of connected components in its complement.
-/
@[simps]
def componentComplFunctor : (Finset V)ᵒᵖ ⥤ Type u where
  obj K := G.ComponentCompl K.unop
  map f := ComponentCompl.hom (le_of_op_hom f)
  map_id _ := funext fun C => C.hom_refl
  map_comp {_ Y Z} h h' := funext fun C => by
    convert C.hom_trans (le_of_op_hom h) (le_of_op_hom _)
    exact h'

/-- The end of a graph, defined as the sections of the functor `component_compl_functor` . -/
protected def «end» :=
  (componentComplFunctor G).sections

theorem end_hom_mk_of_mk {s} (sec : s ∈ G.end) {K L : (Finset V)ᵒᵖ} (h : L ⟶ K) {v : V}
    (vnL : v ∉ L.unop) (hs : s L = G.componentComplMk vnL) :
    s K = G.componentComplMk (Set.notMem_subset (le_of_op_hom h : _ ⊆ _) vnL) := by
  rw [← sec h, hs]
  apply ComponentCompl.hom_mk _ (le_of_op_hom h : _ ⊆ _)

theorem infinite_iff_in_eventualRange {K : (Finset V)ᵒᵖ} (C : G.componentComplFunctor.obj K) :
    C.supp.Infinite ↔ C ∈ G.componentComplFunctor.eventualRange K := by
  simp only [C.infinite_iff_in_all_ranges, CategoryTheory.Functor.eventualRange, Set.mem_iInter,
    Set.mem_range, componentComplFunctor_map]
  exact
    ⟨fun h Lop KL => h Lop.unop (le_of_op_hom KL), fun h L KL =>
      h (Opposite.op L) (opHomOfLE KL)⟩

end Ends

end SimpleGraph
