/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Connected.Basic

/-!
# Totally disconnected and totally separated topological spaces

## Main definitions
We define the following properties for sets in a topological space:

* `IsTotallyDisconnected`: all of its connected components are singletons.
* `IsTotallySeparated`: any two points can be separated by two disjoint opens that cover the set.

For both of these definitions, we also have a class stating that the whole space
satisfies that property: `TotallyDisconnectedSpace`, `TotallySeparatedSpace`.
-/

open Set Function

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, ie either empty or a singleton. -/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton
#align is_totally_disconnected IsTotallyDisconnected

theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim
#align is_totally_disconnected_empty isTotallyDisconnected_empty

theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht
#align is_totally_disconnected_singleton isTotallyDisconnected_singleton

/-- A space is totally disconnected if all of its connected components are singletons. -/
@[mk_iff]
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally disconnected space is totally disconnected. -/
  isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)
#align totally_disconnected_space TotallyDisconnectedSpace

theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α}
    (h : IsPreconnected s) : s.Subsingleton :=
  TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h
#align is_preconnected.subsingleton IsPreconnected.subsingleton

instance Pi.totallyDisconnectedSpace {α : Type*} {β : α → Type*}
    [∀ a, TopologicalSpace (β a)] [∀ a, TotallyDisconnectedSpace (β a)] :
    TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t _ h2 =>
    have this : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩
#align pi.totally_disconnected_space Pi.totallyDisconnectedSpace

instance Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩
#align prod.totally_disconnected_space Prod.totallyDisconnectedSpace

instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (Sum α β) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

instance [∀ i, TopologicalSpace (π i)] [∀ i, TotallyDisconnectedSpace (π i)] :
    TotallyDisconnectedSpace (Σi, π i) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

-- Porting note: reformulated using `Pairwise`
/-- Let `X` be a topological space, and suppose that for all distinct `x,y ∈ X`, there
  is some clopen set `U` such that `x ∈ U` and `y ∉ U`. Then `X` is totally disconnected. -/
theorem isTotallyDisconnected_of_isClopen_set {X : Type*} [TopologicalSpace X]
    (hX : Pairwise fun x y => ∃ (U : Set X), IsClopen U ∧ x ∈ U ∧ y ∉ U) :
    IsTotallyDisconnected (Set.univ : Set X) := by
  rintro S - hS
  unfold Set.Subsingleton
  by_contra! h_contra
  rcases h_contra with ⟨x, hx, y, hy, hxy⟩
  obtain ⟨U, hU, hxU, hyU⟩ := hX hxy
  specialize
    hS U Uᶜ hU.2 hU.compl.2 (fun a _ => em (a ∈ U)) ⟨x, hx, hxU⟩ ⟨y, hy, hyU⟩
  rw [inter_compl_self, Set.inter_empty] at hS
  exact Set.not_nonempty_empty hS
#align is_totally_disconnected_of_clopen_set isTotallyDisconnected_of_isClopen_set

/-- A space is totally disconnected iff its connected components are subsingletons. -/
theorem totallyDisconnectedSpace_iff_connectedComponent_subsingleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, (connectedComponent x).Subsingleton := by
  constructor
  · intro h x
    apply h.1
    · exact subset_univ _
    exact isPreconnected_connectedComponent
  intro h; constructor
  intro s s_sub hs
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, x_in⟩)
  · exact subsingleton_empty
  · exact (h x).anti (hs.subset_connectedComponent x_in)
#align totally_disconnected_space_iff_connected_component_subsingleton totallyDisconnectedSpace_iff_connectedComponent_subsingleton

/-- A space is totally disconnected iff its connected components are singletons. -/
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, connectedComponent x = {x} := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent
#align totally_disconnected_space_iff_connected_component_singleton totallyDisconnectedSpace_iff_connectedComponent_singleton

@[simp] theorem connectedComponent_eq_singleton [TotallyDisconnectedSpace α] (x : α) :
    connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x
#align connected_component_eq_singleton connectedComponent_eq_singleton

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
theorem Continuous.image_connectedComponent_eq_singleton {β : Type*} [TopologicalSpace β]
    [TotallyDisconnectedSpace β] {f : α → β} (h : Continuous f) (a : α) :
    f '' connectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton
#align continuous.image_connected_component_eq_singleton Continuous.image_connectedComponent_eq_singleton

theorem isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht
#align is_totally_disconnected_of_totally_disconnected_space isTotallyDisconnected_of_totallyDisconnectedSpace

theorem isTotallyDisconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s)
    (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun _t hts ht _x x_in _y y_in =>
  hf' <|
    h _ (image_subset f hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)
#align is_totally_disconnected_of_image isTotallyDisconnected_of_image

theorem Embedding.isTotallyDisconnected [TopologicalSpace β] {f : α → β} (hf : Embedding f)
    {s : Set α} (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  isTotallyDisconnected_of_image hf.continuous.continuousOn hf.inj h
#align embedding.is_totally_disconnected Embedding.isTotallyDisconnected

lemma Embedding.isTotallyDisconnected_image [TopologicalSpace β] {f : α → β} (hf : Embedding f)
    {s : Set α} : IsTotallyDisconnected (f '' s) ↔ IsTotallyDisconnected s := by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu ↦ ?_⟩
  obtain ⟨v, hvs, rfl⟩ : ∃ v, v ⊆ s ∧ f '' v = u :=
    ⟨f ⁻¹' u ∩ s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.toInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _

lemma Embedding.isTotallyDisconnected_range [TopologicalSpace β] {f : α → β} (hf : Embedding f) :
    IsTotallyDisconnected (range f) ↔ TotallyDisconnectedSpace α := by
  rw [totallyDisconnectedSpace_iff, ← image_univ, hf.isTotallyDisconnected_image]

lemma totallyDisconnectedSpace_subtype_iff {s : Set α} :
    TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  rw [← embedding_subtype_val.isTotallyDisconnected_range, Subtype.range_val]

instance Subtype.totallyDisconnectedSpace {α : Type*} {p : α → Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
#align subtype.totally_disconnected_space Subtype.totallyDisconnectedSpace

end TotallyDisconnected

section TotallySeparated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def IsTotallySeparated (s : Set α) : Prop :=
  Set.Pairwise s fun x y =>
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ Disjoint u v
#align is_totally_separated IsTotallySeparated

theorem isTotallySeparated_empty : IsTotallySeparated (∅ : Set α) := fun _ => False.elim
#align is_totally_separated_empty isTotallySeparated_empty

theorem isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim
#align is_totally_separated_singleton isTotallySeparated_singleton

theorem isTotallyDisconnected_of_isTotallySeparated {s : Set α} (H : IsTotallySeparated s) :
    IsTotallyDisconnected s := by
  intro t hts ht x x_in y y_in
  by_contra h
  obtain
    ⟨u : Set α, v : Set α, hu : IsOpen u, hv : IsOpen v, hxu : x ∈ u, hyv : y ∈ v, hs : s ⊆ u ∪ v,
      huv⟩ :=
    H (hts x_in) (hts y_in) h
  refine (ht _ _ hu hv (hts.trans hs) ⟨x, x_in, hxu⟩ ⟨y, y_in, hyv⟩).ne_empty ?_
  rw [huv.inter_eq, inter_empty]
#align is_totally_disconnected_of_is_totally_separated isTotallyDisconnected_of_isTotallySeparated

alias IsTotallySeparated.isTotallyDisconnected := isTotallyDisconnected_of_isTotallySeparated
#align is_totally_separated.is_totally_disconnected IsTotallySeparated.isTotallyDisconnected

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally separated space is totally separated. -/
  isTotallySeparated_univ : IsTotallySeparated (univ : Set α)
#align totally_separated_space TotallySeparatedSpace

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.totallyDisconnectedSpace (α : Type u)
    [TopologicalSpace α] [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨TotallySeparatedSpace.isTotallySeparated_univ.isTotallyDisconnected⟩
#align totally_separated_space.totally_disconnected_space TotallySeparatedSpace.totallyDisconnectedSpace

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type*) [TopologicalSpace α]
    [DiscreteTopology α] : TotallySeparatedSpace α :=
  ⟨fun _ _ b _ h => ⟨{b}ᶜ, {b}, isOpen_discrete _, isOpen_discrete _, h, rfl,
    (compl_union_self _).symm.subset, disjoint_compl_left⟩⟩
#align totally_separated_space.of_discrete TotallySeparatedSpace.of_discrete

theorem exists_isClopen_of_totally_separated {α : Type*} [TopologicalSpace α]
    [TotallySeparatedSpace α] {x y : α} (hxy : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ x ∈ U ∧ y ∈ Uᶜ := by
  obtain ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ :=
    TotallySeparatedSpace.isTotallySeparated_univ (Set.mem_univ x) (Set.mem_univ y) hxy
  have hU := isClopen_inter_of_disjoint_cover_clopen isClopen_univ f hU hV disj
  rw [univ_inter _] at hU
  rw [← Set.subset_compl_iff_disjoint_right, subset_compl_comm] at disj
  exact ⟨U, hU, Ux, disj Vy⟩
#align exists_clopen_of_totally_separated exists_isClopen_of_totally_separated

end TotallySeparated


variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}

theorem Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α)
    (hab : connectedComponent a = connectedComponent b) : f a = f b :=
  singleton_eq_singleton_iff.1 <|
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl
#align continuous.image_eq_of_connected_component_eq Continuous.image_eq_of_connectedComponent_eq

/--
The lift to `connectedComponents α` of a continuous map from `α` to a totally disconnected space
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq
#align continuous.connected_components_lift Continuous.connectedComponentsLift

@[continuity]
theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :
    Continuous h.connectedComponentsLift :=
  h.quotient_liftOn' <| by convert h.image_eq_of_connectedComponent_eq
#align continuous.connected_components_lift_continuous Continuous.connectedComponentsLift_continuous

@[simp]
theorem Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) :
    h.connectedComponentsLift x = f x :=
  rfl
#align continuous.connected_components_lift_apply_coe Continuous.connectedComponentsLift_apply_coe

@[simp]
theorem Continuous.connectedComponentsLift_comp_coe (h : Continuous f) :
    h.connectedComponentsLift ∘ (↑) = f :=
  rfl
#align continuous.connected_components_lift_comp_coe Continuous.connectedComponentsLift_comp_coe

theorem connectedComponents_lift_unique' {β : Sort*} {g₁ g₂ : ConnectedComponents α → β}
    (hg : g₁ ∘ ((↑) : α → ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg
#align connected_components_lift_unique' connectedComponents_lift_unique'

theorem Continuous.connectedComponentsLift_unique (h : Continuous f) (g : ConnectedComponents α → β)
    (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift :=
  connectedComponents_lift_unique' <| hg.trans h.connectedComponentsLift_comp_coe.symm
#align continuous.connected_components_lift_unique Continuous.connectedComponentsLift_unique


instance ConnectedComponents.totallyDisconnectedSpace :
    TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.quotientMap_coe.image_connectedComponent, ←
    connectedComponents_preimage_singleton, image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine ConnectedComponents.surjective_coe.forall.2 fun y => ?_
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent
#align connected_components.totally_disconnected_space ConnectedComponents.totallyDisconnectedSpace

/-- Functoriality of `connectedComponents` -/
def Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)
#align continuous.connected_components_map Continuous.connectedComponentsMap

theorem Continuous.connectedComponentsMap_continuous {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : Continuous h.connectedComponentsMap :=
  Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)
#align continuous.connected_components_map_continuous Continuous.connectedComponentsMap_continuous

/-- A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s` -/
theorem IsPreconnected.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
    (hs : IsPreconnected s) {f : α → Y} (hf : ContinuousOn f s) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)
#align is_preconnected.constant IsPreconnected.constant

/-- A `PreconnectedSpace` version of `isPreconnected.constant` -/
theorem PreconnectedSpace.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (hp : PreconnectedSpace α) {f : α → Y} (hf : Continuous f) {x y : α} : f x = f y :=
  IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial
#align preconnected_space.constant PreconnectedSpace.constant

/-- Refinement of `IsPreconnected.constant` only assuming the map factors through a
discrete subset of the target. -/
theorem IsPreconnected.constant_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S) (hTm : MapsTo f S T)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  let F : S → T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.restrict_mapsTo _)
#align is_preconnected.constant_of_maps_to IsPreconnected.constant_of_mapsTo

/-- A version of `IsPreconnected.constant_of_mapsTo` that assumes that the codomain is nonempty and
proves that `f` is equal to `const α y` on `S` for some `y ∈ T`. -/
theorem IsPreconnected.eqOn_const_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S) (hTm : MapsTo f S T)
    (hne : T.Nonempty) : ∃ y ∈ T, EqOn f (const α y) S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hc hTm hx' hx⟩
