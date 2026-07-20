/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen

/-!
# Locally connected topological spaces

A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Local connectivity is equivalent to each point having a basis
of connected (not necessarily open) sets --- but in a non-trivial way, so we choose this definition
and prove the equivalence later in `locallyConnectedSpace_iff_connected_basis`.
-/

public section

open Set Topology

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {X : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section LocallyConnectedSpace

/-- A topological space is **locally connected** if each neighborhood filter admits a basis
of connected *open* sets. Note that it is equivalent to each point having a basis of connected
(not necessarily open) sets but in a non-trivial way, so we choose this definition and prove the
equivalence later in `locallyConnectedSpace_iff_connected_basis`. -/
class LocallyConnectedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- Open connected neighborhoods form a basis of the neighborhoods filter. -/
  open_connected_basis : ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id

theorem locallyConnectedSpace_iff_hasBasis_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => IsOpen s ∧ x ∈ s ∧ IsConnected s) id :=
  ⟨@LocallyConnectedSpace.open_connected_basis _ _, LocallyConnectedSpace.mk⟩

theorem locallyConnectedSpace_iff_subsets_isOpen_isConnected :
    LocallyConnectedSpace α ↔
      ∀ x, ∀ U ∈ 𝓝 x, ∃ V : Set α, V ⊆ U ∧ IsOpen V ∧ x ∈ V ∧ IsConnected V := by
  simp_rw [locallyConnectedSpace_iff_hasBasis_isOpen_isConnected]
  refine forall_congr' fun _ => ?_
  constructor
  · intro h U hU
    rcases h.mem_iff.mp hU with ⟨V, hV, hVU⟩
    exact ⟨V, hVU, hV⟩
  · exact fun h => ⟨fun U => ⟨fun hU =>
      let ⟨V, hVU, hV⟩ := h U hU
      ⟨V, hV, hVU⟩, fun ⟨V, ⟨hV, hxV, _⟩, hVU⟩ => mem_nhds_iff.mpr ⟨V, hVU, hV, hxV⟩⟩⟩

/-- A space with discrete topology is a locally connected space. -/
instance (priority := 100) DiscreteTopology.toLocallyConnectedSpace (α) [TopologicalSpace α]
    [DiscreteTopology α] : LocallyConnectedSpace α :=
  locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x _U hU =>
    ⟨{x}, singleton_subset_iff.2 <| mem_of_mem_nhds hU, isOpen_discrete _, rfl,
      isConnected_singleton⟩

theorem connectedComponentIn_mem_nhds [LocallyConnectedSpace α] {F : Set α} {x : α} (h : F ∈ 𝓝 x) :
    connectedComponentIn F x ∈ 𝓝 x := by
  rw [(LocallyConnectedSpace.open_connected_basis x).mem_iff] at h
  rcases h with ⟨s, ⟨h1s, hxs, h2s⟩, hsF⟩
  exact mem_nhds_iff.mpr ⟨s, h2s.isPreconnected.subset_connectedComponentIn hxs hsF, h1s, hxs⟩

protected theorem IsOpen.connectedComponentIn [LocallyConnectedSpace α] {F : Set α} {x : α}
    (hF : IsOpen F) : IsOpen (connectedComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [connectedComponentIn_eq hy]
  exact connectedComponentIn_mem_nhds (hF.mem_nhds <| connectedComponentIn_subset F x hy)

theorem isOpen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsOpen (connectedComponent x) := by
  rw [← connectedComponentIn_univ]
  exact isOpen_univ.connectedComponentIn

theorem isClopen_connectedComponent [LocallyConnectedSpace α] {x : α} :
    IsClopen (connectedComponent x) :=
  ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩

theorem locallyConnectedSpace_iff_connectedComponentIn_open :
    LocallyConnectedSpace α ↔
      ∀ F : Set α, IsOpen F → ∀ x ∈ F, IsOpen (connectedComponentIn F x) := by
  constructor
  · intro h
    exact fun F hF x _ => hF.connectedComponentIn
  · intro h
    rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    refine fun x U hU =>
        ⟨connectedComponentIn (interior U) x,
          (connectedComponentIn_subset _ _).trans interior_subset, h _ isOpen_interior x ?_,
          mem_connectedComponentIn ?_, isConnected_connectedComponentIn_iff.mpr ?_⟩ <;>
      exact mem_interior_iff_mem_nhds.mpr hU

theorem locallyConnectedSpace_iff_connected_subsets :
    LocallyConnectedSpace α ↔ ∀ (x : α), ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, IsPreconnected V ∧ V ⊆ U := by
  constructor
  · rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
    intro h x U hxU
    rcases h x U hxU with ⟨V, hVU, hV₁, hxV, hV₂⟩
    exact ⟨V, hV₁.mem_nhds hxV, hV₂.isPreconnected, hVU⟩
  · rw [locallyConnectedSpace_iff_connectedComponentIn_open]
    refine fun h U hU x _ => isOpen_iff_mem_nhds.mpr fun y hy => ?_
    rw [connectedComponentIn_eq hy]
    rcases h y U (hU.mem_nhds <| (connectedComponentIn_subset _ _) hy) with ⟨V, hVy, hV, hVU⟩
    exact Filter.mem_of_superset hVy (hV.subset_connectedComponentIn (mem_of_mem_nhds hVy) hVU)

theorem locallyConnectedSpace_iff_connected_basis :
    LocallyConnectedSpace α ↔
      ∀ x, (𝓝 x).HasBasis (fun s : Set α => s ∈ 𝓝 x ∧ IsPreconnected s) id := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  exact forall_congr' fun x => Filter.hasBasis_self.symm

theorem locallyConnectedSpace_of_connected_bases {ι : Type*} (b : α → ι → Set α) (p : α → ι → Prop)
    (hbasis : ∀ x, (𝓝 x).HasBasis (p x) (b x))
    (hconnected : ∀ x i, p x i → IsPreconnected (b x i)) : LocallyConnectedSpace α := by
  rw [locallyConnectedSpace_iff_connected_basis]
  exact fun x =>
    (hbasis x).to_hasBasis
      (fun i hi => ⟨b x i, ⟨(hbasis x).mem_of_mem hi, hconnected x i hi⟩, subset_rfl⟩) fun s hs =>
      ⟨(hbasis x).index s hs.1, ⟨(hbasis x).property_index hs.1, (hbasis x).set_index_subset hs.1⟩⟩

theorem TopologicalSpace.IsTopologicalBasis.isOpen_isPreconnected [LocallyConnectedSpace α] :
    TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} :=
  .of_hasBasis_nhds fun x =>
    (LocallyConnectedSpace.open_connected_basis x).congr
      (by grind [IsConnected, Set.Nonempty])
      (fun _ _ => rfl)

theorem locallyConnectedSpace_iff_isTopologicalBasis_isOpen_isPreconnected :
    LocallyConnectedSpace α ↔
      TopologicalSpace.IsTopologicalBasis {s : Set α | IsOpen s ∧ IsPreconnected s} where
  mp _ := .isOpen_isPreconnected
  mpr h := ⟨fun _ => h.nhds_hasBasis.congr (by grind [IsConnected, Set.Nonempty]) (fun _ _ => rfl)⟩

lemma Topology.IsOpenEmbedding.locallyConnectedSpace [LocallyConnectedSpace α] [TopologicalSpace β]
    {f : β → α} (h : IsOpenEmbedding f) : LocallyConnectedSpace β := by
  refine locallyConnectedSpace_of_connected_bases (fun _ s ↦ f ⁻¹' s)
    (fun x s ↦ (IsOpen s ∧ f x ∈ s ∧ IsConnected s) ∧ s ⊆ range f) (fun x ↦ ?_)
    (fun x s hxs ↦ hxs.1.2.2.isPreconnected.preimage_of_isOpenMap h.injective h.isOpenMap hxs.2)
  rw [h.nhds_eq_comap]
  exact LocallyConnectedSpace.open_connected_basis (f x) |>.restrict_subset
    (h.isOpen_range.mem_nhds <| mem_range_self _) |>.comap _

theorem IsOpen.locallyConnectedSpace [LocallyConnectedSpace α] {U : Set α} (hU : IsOpen U) :
    LocallyConnectedSpace U :=
  hU.isOpenEmbedding_subtypeVal.locallyConnectedSpace

/-- The image of a locally connected space under a quotient map is locally connected. -/
theorem Topology.IsQuotientMap.locallyConnectedSpace [LocallyConnectedSpace α]
    [TopologicalSpace β] {f : α → β} (hf : IsQuotientMap f) : LocallyConnectedSpace β := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF y _
  rw [← hf.isOpen_preimage, isOpen_iff_mem_nhds]
  intro x hx
  have hxF : x ∈ f ⁻¹' F := connectedComponentIn_subset F y hx
  refine Filter.mem_of_superset
    ((hF.preimage hf.continuous).connectedComponentIn.mem_nhds (mem_connectedComponentIn hxF))
    fun z hz ↦ ?_
  rw [mem_preimage, connectedComponentIn_eq hx]
  exact connectedComponentIn_mono _ (image_preimage_subset f F)
    (hf.continuous.mapsTo_connectedComponentIn hxF hz)

/-- If a space is locally connected, the topology of its connected components is discrete. -/
instance [LocallyConnectedSpace α] : DiscreteTopology <| ConnectedComponents α := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  simp [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton, isOpen_connectedComponent]

/-- A locally connected compact space has finitely many connected components. -/
instance [LocallyConnectedSpace α] [CompactSpace α] : Finite <| ConnectedComponents α :=
  finite_of_compact_of_discrete

/-- The product of two locally connected spaces is locally connected. -/
instance Prod.locallyConnectedSpace [TopologicalSpace β] [LocallyConnectedSpace α]
    [LocallyConnectedSpace β] : LocallyConnectedSpace (α × β) := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  rintro ⟨x, y⟩ U hU
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
  exact ⟨connectedComponentIn u x ×ˢ connectedComponentIn v y,
    prod_mem_nhds (connectedComponentIn_mem_nhds hu) (connectedComponentIn_mem_nhds hv),
    isPreconnected_connectedComponentIn.prod isPreconnected_connectedComponentIn,
    (prod_mono (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)).trans huv⟩

/-- If each `X i` is locally connected and all but finitely many are preconnected, then
`∀ i, X i` is locally connected. -/
theorem Pi.locallyConnectedSpace_of_finite_nonpreconnected [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] (hfinite : {i | ¬PreconnectedSpace (X i)}.Finite) :
    LocallyConnectedSpace (∀ i, X i) := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨J, hJ, t, ht, htU⟩ := hU
  classical
  set K := J ∪ {i | ¬PreconnectedSpace (X i)} with hK
  refine ⟨K.pi fun i ↦ connectedComponentIn (t i) (x i),
    set_pi_mem_nhds (hJ.union hfinite) fun i _ ↦ connectedComponentIn_mem_nhds (ht i), ?_,
    fun f hf ↦ htU fun i hiJ ↦ connectedComponentIn_subset _ _ (hf i (mem_union_left _ hiJ))⟩
  rw [← univ_pi_piecewise_univ]
  refine isPreconnected_univ_pi fun i ↦ ?_
  by_cases hi : i ∈ K
  · rw [piecewise_eq_of_mem _ _ _ hi]
    exact isPreconnected_connectedComponentIn
  · rw [piecewise_eq_of_notMem _ _ _ hi]
    have : PreconnectedSpace (X i) := not_not.mp fun h ↦ hi (hK ▸ mem_union_right _ h)
    exact isPreconnected_univ

/-- A finite product of locally connected spaces is locally connected. -/
instance Pi.locallyConnectedSpace_of_finite [Finite ι] [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] : LocallyConnectedSpace (∀ i, X i) :=
  locallyConnectedSpace_of_finite_nonpreconnected (Set.toFinite _)

/-- A product of preconnected, locally connected spaces is locally connected. Note that an
arbitrary product of locally connected spaces need not be locally connected, so the
preconnectedness assumption cannot be dropped entirely (though it can be dropped for finitely
many factors, see `Pi.locallyConnectedSpace_of_finite_nonpreconnected`). -/
instance Pi.locallyConnectedSpace [∀ i, TopologicalSpace (X i)]
    [∀ i, LocallyConnectedSpace (X i)] [∀ i, PreconnectedSpace (X i)] :
    LocallyConnectedSpace (∀ i, X i) :=
  locallyConnectedSpace_of_finite_nonpreconnected
    (Set.finite_empty.subset fun _ hi ↦ (hi inferInstance).elim)

/-- A product of spaces is locally connected iff it is empty, or every factor is locally
connected and all but finitely many factors are preconnected. -/
theorem Pi.locallyConnectedSpace_iff [∀ i, TopologicalSpace (X i)] :
    LocallyConnectedSpace (∀ i, X i) ↔
      IsEmpty (∀ i, X i) ∨
        (∀ i, LocallyConnectedSpace (X i)) ∧ {i | ¬PreconnectedSpace (X i)}.Finite := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases isEmpty_or_nonempty (∀ i, X i) with he | hne
    · exact .inl he
    obtain ⟨x⟩ := hne
    classical
    haveI : ∀ i, Nonempty (X i) := Classical.nonempty_pi.mp ⟨x⟩
    refine .inr ⟨fun i ↦ ((isOpenMap_eval i).isQuotientMap (continuous_apply i)
      (Function.surjective_eval i)).locallyConnectedSpace, ?_⟩
    have hVn : connectedComponent x ∈ 𝓝 x :=
      isOpen_connectedComponent.mem_nhds mem_connectedComponent
    rw [nhds_pi, Filter.mem_pi] at hVn
    obtain ⟨J, hJ, t, ht, htV⟩ := hVn
    refine hJ.subset fun i hi ↦ by_contra fun hiJ ↦ hi ?_
    suffices himg : Function.eval i '' connectedComponent x = univ by
      exact ⟨himg ▸ isPreconnected_connectedComponent.image _ (continuous_apply i).continuousOn⟩
    refine (subset_univ _).antisymm fun z _ ↦
      ⟨Function.update x i z, htV fun j hj ↦ ?_, by simp⟩
    rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
    exact mem_of_mem_nhds (ht j)
  · rintro (he | ⟨hloc, hfin⟩)
    · exact ⟨fun x ↦ he.elim x⟩
    · haveI := hloc
      exact Pi.locallyConnectedSpace_of_finite_nonpreconnected hfin

end LocallyConnectedSpace
