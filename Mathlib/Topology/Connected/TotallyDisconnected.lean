/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Topology.Connected.Clopen

/-!
# Totally disconnected and totally separated topological spaces

## Main definitions
We define the following properties for sets in a topological space:

* `IsTotallyDisconnected`: all of its connected components are singletons.
* `IsTotallySeparated`: any two points can be separated by two disjoint opens that cover the set.

For both of these definitions, we also have a class stating that the whole space
satisfies that property: `TotallyDisconnectedSpace`, `TotallySeparatedSpace`.
-/

open Function Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section TotallyDisconnected

/-- A set `s` is called totally disconnected if every subset `t ⊆ s` which is preconnected is
a subsingleton, i.e. either empty or a singleton. -/
def IsTotallyDisconnected (s : Set α) : Prop :=
  ∀ t, t ⊆ s → IsPreconnected t → t.Subsingleton

theorem isTotallyDisconnected_empty : IsTotallyDisconnected (∅ : Set α) := fun _ ht _ _ x_in _ _ =>
  (ht x_in).elim

theorem isTotallyDisconnected_singleton {x} : IsTotallyDisconnected ({x} : Set α) := fun _ ht _ =>
  subsingleton_singleton.anti ht

/-- A space is totally disconnected if all of its connected components are singletons. -/
@[mk_iff]
class TotallyDisconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally disconnected space is totally disconnected. -/
  isTotallyDisconnected_univ : IsTotallyDisconnected (univ : Set α)

theorem IsPreconnected.subsingleton [TotallyDisconnectedSpace α] {s : Set α}
    (h : IsPreconnected s) : s.Subsingleton :=
  TotallyDisconnectedSpace.isTotallyDisconnected_univ s (subset_univ s) h

instance Pi.totallyDisconnectedSpace {α : Type*} {β : α → Type*}
    [∀ a, TopologicalSpace (β a)] [∀ a, TotallyDisconnectedSpace (β a)] :
    TotallyDisconnectedSpace (∀ a : α, β a) :=
  ⟨fun t _ h2 =>
    have this : ∀ a, IsPreconnected ((fun x : ∀ a, β a => x a) '' t) := fun a =>
      h2.image (fun x => x a) (continuous_apply a).continuousOn
    fun x x_in y y_in => funext fun a => (this a).subsingleton ⟨x, x_in, rfl⟩ ⟨y, y_in, rfl⟩⟩

instance Prod.totallyDisconnectedSpace [TopologicalSpace β] [TotallyDisconnectedSpace α]
    [TotallyDisconnectedSpace β] : TotallyDisconnectedSpace (α × β) :=
  ⟨fun t _ h2 =>
    have H1 : IsPreconnected (Prod.fst '' t) := h2.image Prod.fst continuous_fst.continuousOn
    have H2 : IsPreconnected (Prod.snd '' t) := h2.image Prod.snd continuous_snd.continuousOn
    fun x hx y hy =>
    Prod.ext (H1.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)
      (H2.subsingleton ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)⟩

instance [TopologicalSpace β] [TotallyDisconnectedSpace α] [TotallyDisconnectedSpace β] :
    TotallyDisconnectedSpace (α ⊕ β) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isPreconnected_iff.1 hs
  · exact ht.subsingleton.image _
  · exact ht.subsingleton.image _

instance [∀ i, TopologicalSpace (X i)] [∀ i, TotallyDisconnectedSpace (X i)] :
    TotallyDisconnectedSpace (Σi, X i) := by
  refine ⟨fun s _ hs => ?_⟩
  obtain rfl | h := s.eq_empty_or_nonempty
  · exact subsingleton_empty
  · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
    exact ht.isPreconnected.subsingleton.image _

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

/-- A space is totally disconnected iff its connected components are singletons. -/
theorem totallyDisconnectedSpace_iff_connectedComponent_singleton :
    TotallyDisconnectedSpace α ↔ ∀ x : α, connectedComponent x = {x} := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_subsingleton]
  refine forall_congr' fun x => ?_
  rw [subsingleton_iff_singleton]
  exact mem_connectedComponent

@[simp] theorem connectedComponent_eq_singleton [TotallyDisconnectedSpace α] (x : α) :
    connectedComponent x = {x} :=
  totallyDisconnectedSpace_iff_connectedComponent_singleton.1 ‹_› x

/-- The image of a connected component in a totally disconnected space is a singleton. -/
@[simp]
theorem Continuous.image_connectedComponent_eq_singleton {β : Type*} [TopologicalSpace β]
    [TotallyDisconnectedSpace β] {f : α → β} (h : Continuous f) (a : α) :
    f '' connectedComponent a = {f a} :=
  (Set.subsingleton_iff_singleton <| mem_image_of_mem f mem_connectedComponent).mp
    (isPreconnected_connectedComponent.image f h.continuousOn).subsingleton

theorem isTotallyDisconnected_of_totallyDisconnectedSpace [TotallyDisconnectedSpace α] (s : Set α) :
    IsTotallyDisconnected s := fun t _ ht =>
  TotallyDisconnectedSpace.isTotallyDisconnected_univ _ t.subset_univ ht

lemma TotallyDisconnectedSpace.eq_of_continuous [TopologicalSpace β]
    [PreconnectedSpace α] [TotallyDisconnectedSpace β] (f : α → β) (hf : Continuous f)
    (i j : α) : f i = f j :=
  (isPreconnected_univ.image f hf.continuousOn).subsingleton ⟨i, trivial, rfl⟩ ⟨j, trivial, rfl⟩

/-- The bijection `C(X, Y) ≃ Y` when `Y` is totally disconnected and `X` is connected. -/
@[simps! symm_apply_apply]
noncomputable def TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace
    (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] [TotallyDisconnectedSpace Y] [ConnectedSpace X] :
    C(X, Y) ≃ Y where
  toFun f := f (Classical.arbitrary _)
  invFun y := ⟨fun _ ↦ y, by continuity⟩
  left_inv f := ContinuousMap.ext (TotallyDisconnectedSpace.eq_of_continuous _ f.2 _)
  right_inv _ := rfl

theorem isTotallyDisconnected_of_image [TopologicalSpace β] {f : α → β} (hf : ContinuousOn f s)
    (hf' : Injective f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  fun _t hts ht _x x_in _y y_in =>
  hf' <|
    h _ (image_mono hts) (ht.image f <| hf.mono hts) (mem_image_of_mem f x_in)
      (mem_image_of_mem f y_in)

lemma Topology.IsEmbedding.isTotallyDisconnected [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : IsEmbedding f) (h : IsTotallyDisconnected (f '' s)) : IsTotallyDisconnected s :=
  isTotallyDisconnected_of_image hf.continuous.continuousOn hf.injective h

lemma Topology.IsEmbedding.isTotallyDisconnected_image [TopologicalSpace β] {f : α → β} {s : Set α}
    (hf : IsEmbedding f) : IsTotallyDisconnected (f '' s) ↔ IsTotallyDisconnected s := by
  refine ⟨hf.isTotallyDisconnected, fun hs u hus hu ↦ ?_⟩
  obtain ⟨v, hvs, rfl⟩ : ∃ v, v ⊆ s ∧ f '' v = u :=
    ⟨f ⁻¹' u ∩ s, inter_subset_right, by rwa [image_preimage_inter, inter_eq_left]⟩
  rw [hf.isInducing.isPreconnected_image] at hu
  exact (hs v hvs hu).image _

lemma Topology.IsEmbedding.isTotallyDisconnected_range [TopologicalSpace β] {f : α → β}
    (hf : IsEmbedding f) : IsTotallyDisconnected (range f) ↔ TotallyDisconnectedSpace α := by
  rw [totallyDisconnectedSpace_iff, ← image_univ, hf.isTotallyDisconnected_image]

lemma totallyDisconnectedSpace_subtype_iff {s : Set α} :
    TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  rw [← IsEmbedding.subtypeVal.isTotallyDisconnected_range, Subtype.range_val]

instance Subtype.totallyDisconnectedSpace {α : Type*} {p : α → Prop} [TopologicalSpace α]
    [TotallyDisconnectedSpace α] : TotallyDisconnectedSpace (Subtype p) :=
  totallyDisconnectedSpace_subtype_iff.2 (isTotallyDisconnected_of_totallyDisconnectedSpace _)

end TotallyDisconnected

section TotallySeparated

/-- A set `s` is called totally separated if any two points of this set can be separated
by two disjoint open sets covering `s`. -/
def IsTotallySeparated (s : Set α) : Prop :=
  Set.Pairwise s fun x y =>
  ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ x ∈ u ∧ y ∈ v ∧ s ⊆ u ∪ v ∧ Disjoint u v

theorem isTotallySeparated_empty : IsTotallySeparated (∅ : Set α) := fun _ => False.elim

theorem isTotallySeparated_singleton {x} : IsTotallySeparated ({x} : Set α) := fun _ hp _ hq hpq =>
  (hpq <| (eq_of_mem_singleton hp).symm ▸ (eq_of_mem_singleton hq).symm).elim

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

alias IsTotallySeparated.isTotallyDisconnected := isTotallyDisconnected_of_isTotallySeparated

/-- A space is totally separated if any two points can be separated by two disjoint open sets
covering the whole space. -/
@[mk_iff] class TotallySeparatedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a totally separated space is totally separated. -/
  isTotallySeparated_univ : IsTotallySeparated (univ : Set α)

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.totallyDisconnectedSpace (α : Type u)
    [TopologicalSpace α] [TotallySeparatedSpace α] : TotallyDisconnectedSpace α :=
  ⟨TotallySeparatedSpace.isTotallySeparated_univ.isTotallyDisconnected⟩

-- see Note [lower instance priority]
instance (priority := 100) TotallySeparatedSpace.of_discrete (α : Type*) [TopologicalSpace α]
    [DiscreteTopology α] : TotallySeparatedSpace α :=
  ⟨fun _ _ b _ h => ⟨{b}ᶜ, {b}, isOpen_discrete _, isOpen_discrete _, h, rfl,
    (compl_union_self _).symm.subset, disjoint_compl_left⟩⟩

theorem totallySeparatedSpace_iff_exists_isClopen {α : Type*} [TopologicalSpace α] :
    TotallySeparatedSpace α ↔ Pairwise (∃ U : Set α, IsClopen U ∧ · ∈ U ∧ · ∈ Uᶜ) := by
  simp only [totallySeparatedSpace_iff, IsTotallySeparated, Set.Pairwise, mem_univ, true_implies]
  refine forall₃_congr fun x y _ ↦
    ⟨fun ⟨U, V, hU, hV, Ux, Vy, f, disj⟩ ↦ ?_, fun ⟨U, hU, Ux, Ucy⟩ ↦ ?_⟩
  · exact ⟨U, isClopen_of_disjoint_cover_open f hU hV disj,
      Ux, fun Uy ↦ Set.disjoint_iff.mp disj ⟨Uy, Vy⟩⟩
  · exact ⟨U, Uᶜ, hU.2, hU.compl.2, Ux, Ucy, (Set.union_compl_self U).ge, disjoint_compl_right⟩

theorem exists_isClopen_of_totally_separated {α : Type*} [TopologicalSpace α]
    [TotallySeparatedSpace α] : Pairwise (∃ U : Set α, IsClopen U ∧ · ∈ U ∧ · ∈ Uᶜ) :=
  totallySeparatedSpace_iff_exists_isClopen.mp ‹_›

/-- Let `X` be a topological space, and suppose that for all distinct `x,y ∈ X`, there
  is some clopen set `U` such that `x ∈ U` and `y ∉ U`. Then `X` is totally disconnected. -/
@[deprecated totallySeparatedSpace_iff_exists_isClopen (since := "2025-04-03")]
theorem isTotallyDisconnected_of_isClopen_set {X : Type*} [TopologicalSpace X]
    (hX : Pairwise (∃ (U : Set X), IsClopen U ∧ · ∈ U ∧ · ∉ U)) :
    IsTotallyDisconnected (Set.univ : Set X) :=
  (totallySeparatedSpace_iff X).mp (totallySeparatedSpace_iff_exists_isClopen.mpr hX)
    |>.isTotallyDisconnected

end TotallySeparated


variable [TopologicalSpace β] [TotallyDisconnectedSpace β] {f : α → β}

theorem Continuous.image_eq_of_connectedComponent_eq (h : Continuous f) (a b : α)
    (hab : connectedComponent a = connectedComponent b) : f a = f b :=
  singleton_eq_singleton_iff.1 <|
    h.image_connectedComponent_eq_singleton a ▸
      h.image_connectedComponent_eq_singleton b ▸ hab ▸ rfl

/--
The lift to `connectedComponents α` of a continuous map from `α` to a totally disconnected space
-/
def Continuous.connectedComponentsLift (h : Continuous f) : ConnectedComponents α → β := fun x =>
  Quotient.liftOn' x f h.image_eq_of_connectedComponent_eq

@[continuity]
theorem Continuous.connectedComponentsLift_continuous (h : Continuous f) :
    Continuous h.connectedComponentsLift :=
  h.quotient_liftOn' <| by convert h.image_eq_of_connectedComponent_eq

@[simp]
theorem Continuous.connectedComponentsLift_apply_coe (h : Continuous f) (x : α) :
    h.connectedComponentsLift x = f x :=
  rfl

@[simp]
theorem Continuous.connectedComponentsLift_comp_coe (h : Continuous f) :
    h.connectedComponentsLift ∘ (↑) = f :=
  rfl

theorem connectedComponents_lift_unique' {β : Sort*} {g₁ g₂ : ConnectedComponents α → β}
    (hg : g₁ ∘ ((↑) : α → ConnectedComponents α) = g₂ ∘ (↑)) : g₁ = g₂ :=
  ConnectedComponents.surjective_coe.injective_comp_right hg

theorem Continuous.connectedComponentsLift_unique (h : Continuous f) (g : ConnectedComponents α → β)
    (hg : g ∘ (↑) = f) : g = h.connectedComponentsLift :=
  connectedComponents_lift_unique' <| hg.trans h.connectedComponentsLift_comp_coe.symm

instance ConnectedComponents.totallyDisconnectedSpace :
    TotallyDisconnectedSpace (ConnectedComponents α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  refine ConnectedComponents.surjective_coe.forall.2 fun x => ?_
  rw [← ConnectedComponents.isQuotientMap_coe.image_connectedComponent, ←
    connectedComponents_preimage_singleton, image_preimage_eq _ ConnectedComponents.surjective_coe]
  refine ConnectedComponents.surjective_coe.forall.2 fun y => ?_
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

/-- Functoriality of `connectedComponents` -/
def Continuous.connectedComponentsMap {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : ConnectedComponents α → ConnectedComponents β :=
  Continuous.connectedComponentsLift (ConnectedComponents.continuous_coe.comp h)

theorem Continuous.connectedComponentsMap_continuous {β : Type*} [TopologicalSpace β] {f : α → β}
    (h : Continuous f) : Continuous h.connectedComponentsMap :=
  Continuous.connectedComponentsLift_continuous (ConnectedComponents.continuous_coe.comp h)

/-- A preconnected set `s` has the property that every map to a
discrete space that is continuous on `s` is constant on `s` -/
theorem IsPreconnected.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y] {s : Set α}
    (hs : IsPreconnected s) {f : α → Y} (hf : ContinuousOn f s) {x y : α} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  (hs.image f hf).subsingleton (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- A `PreconnectedSpace` version of `isPreconnected.constant` -/
theorem PreconnectedSpace.constant {Y : Type*} [TopologicalSpace Y] [DiscreteTopology Y]
    (hp : PreconnectedSpace α) {f : α → Y} (hf : Continuous f) {x y : α} : f x = f y :=
  IsPreconnected.constant hp.isPreconnected_univ (Continuous.continuousOn hf) trivial trivial

/-- Refinement of `IsPreconnected.constant` only assuming the map factors through a
discrete subset of the target. -/
theorem IsPreconnected.constant_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) {x y : α} (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  let F : S → T := hTm.restrict f S T
  suffices F ⟨x, hx⟩ = F ⟨y, hy⟩ by rwa [← Subtype.coe_inj] at this
  exact (isPreconnected_iff_preconnectedSpace.mp hS).constant (hc.mapsToRestrict _)

/-- A version of `IsPreconnected.constant_of_mapsTo` that assumes that the codomain is nonempty and
proves that `f` is equal to `const α y` on `S` for some `y ∈ T`. -/
theorem IsPreconnected.eqOn_const_of_mapsTo {S : Set α} (hS : IsPreconnected S)
    {β} [TopologicalSpace β] {T : Set β} [DiscreteTopology T] {f : α → β} (hc : ContinuousOn f S)
    (hTm : MapsTo f S T) (hne : T.Nonempty) : ∃ y ∈ T, EqOn f (const α y) S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨x, hx⟩)
  · exact hne.imp fun _ hy => ⟨hy, eqOn_empty _ _⟩
  · exact ⟨f x, hTm hx, fun x' hx' => hS.constant_of_mapsTo hc hTm hx' hx⟩
