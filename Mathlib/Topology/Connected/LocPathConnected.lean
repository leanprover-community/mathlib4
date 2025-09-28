/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Ben Eltschig
-/
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.AlexandrovDiscrete

/-!
# Locally path-connected spaces

This file defines `LocPathConnectedSpace X`, a predicate class asserting that `X` is locally
path-connected, in that each point has a basis of path-connected neighborhoods.

## Main results

* `IsOpen.pathComponent` / `IsClosed.pathComponent`: in locally path-connected spaces,
  path-components are both open and closed.
* `pathComponent_eq_connectedComponent`: in locally path-connected spaces, path-components and
  connected components agree.
* `pathConnectedSpace_iff_connectedSpace`: locally path-connected spaces are path-connected iff they
  are connected.
* `instLocallyConnectedSpace`: locally path-connected spaces are also locally connected.
* `IsOpen.locPathConnectedSpace`: open subsets of locally path-connected spaces are
  locally path-connected.
* `LocPathConnectedSpace.coinduced` / `Quotient.locPathConnectedSpace`: quotients of locally
  path-connected spaces are locally path-connected.
* `Sum.locPathConnectedSpace` / `Sigma.locPathConnectedSpace`: disjoint unions of locally
  path-connected spaces are locally path-connected.

Abstractly, this also shows that locally path-connected spaces form a coreflective subcategory of
the category of topological spaces, although we do not prove that in this form here.

## Implementation notes

In the definition of `LocPathConnectedSpace X` we require neighbourhoods in the basis to be
path-connected, but not necessarily open; that they can also be required to be open is shown as
a theorem in `isOpen_isPathConnected_basis`.
-/

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*} {F : Set X}

section LocPathConnectedSpace

/-- A topological space is locally path connected, at every point, path connected
neighborhoods form a neighborhood basis. -/
class LocPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

export LocPathConnectedSpace (path_connected_basis)

theorem LocPathConnectedSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

variable [LocPathConnectedSpace X]

protected theorem IsOpen.pathComponentIn (hF : IsOpen F) (x : X) :
    IsOpen (pathComponentIn F x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
  exact mem_of_superset hs.1.1 <| pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

/-- In a locally path connected space, each path component is an open set. -/
protected theorem IsOpen.pathComponent (x : X) : IsOpen (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

/-- In a locally path connected space, each path component is a closed set. -/
protected theorem IsClosed.pathComponent (x : X) : IsClosed (pathComponent x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
  exact hxy <|  hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

/-- In a locally path connected space, each path component is a clopen set. -/
protected theorem IsClopen.pathComponent (x : X) : IsClopen (pathComponent x) :=
  ⟨.pathComponent x, .pathComponent x⟩

lemma pathComponentIn_mem_nhds (hF : F ∈ 𝓝 x) : pathComponentIn F x ∈ 𝓝 x := by
  let ⟨u, huF, hu, hxu⟩ := mem_nhds_iff.mp hF
  exact mem_nhds_iff.mpr ⟨pathComponentIn u x, pathComponentIn_mono huF,
    hu.pathComponentIn x, mem_pathComponentIn_self hxu⟩

theorem pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ⟨inferInstance, fun x y ↦ ?_⟩⟩
  rw [← mem_pathComponent_iff, (IsClopen.pathComponent _).eq_univ] <;> simp

theorem pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedComponent x :=
  (pathComponent_subset_component x).antisymm <|
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

theorem pathConnected_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

theorem isOpen_isPathConnected_basis (x : X) :
    (𝓝 x).HasBasis (fun s : Set X ↦ IsOpen s ∧ x ∈ s ∧ IsPathConnected s) id := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn u x, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.trans hus⟩

theorem Topology.IsOpenEmbedding.locPathConnectedSpace {e : Y → X} (he : IsOpenEmbedding e) :
    LocPathConnectedSpace Y :=
  have (y : Y) :
      (𝓝 y).HasBasis (fun s ↦ s ∈ 𝓝 (e y) ∧ IsPathConnected s ∧ s ⊆ range e) (e ⁻¹' ·) :=
    he.basis_nhds <| pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ ↦ by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]

theorem IsOpen.locPathConnectedSpace {U : Set X} (h : IsOpen U) : LocPathConnectedSpace U :=
  h.isOpenEmbedding_subtypeVal.locPathConnectedSpace

theorem IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) :
    IsConnected U ↔ IsPathConnected U := by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  haveI := U_op.locPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

/-- Locally path-connected spaces are locally connected. -/
instance : LocallyConnectedSpace X := by
  refine ⟨forall_imp (fun x h ↦ ⟨fun s ↦ ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs ↦ ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ ↦ mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

/-- A space is locally path-connected iff all path components of open subsets are open. -/
lemma locPathConnectedSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔ ∀ (x : X) (u : Set X), IsOpen u → IsOpen (pathComponentIn u x) :=
  ⟨fun _ _ _ hu ↦ hu.pathComponentIn _, fun h ↦ ⟨fun x ↦ ⟨fun s ↦ by
    refine ⟨fun hs ↦ ?_, fun ⟨_, ht⟩ ↦ Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn u x, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_pathComponentIn hu.2.2⟩, pathComponentIn_subset.trans hu.1⟩⟩⟩⟩

/-- A space is locally path-connected iff all path components of open subsets are neighbourhoods. -/
lemma locPathConnectedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔
    ∀ x : X, ∀ u : Set X, IsOpen u → x ∈ u → pathComponentIn u x ∈ nhds x := by
  rw [locPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u ↦ imp_congr_right fun _ ↦ ?_
  exact ⟨fun h x hxu ↦ (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x ↦ isOpen_iff_mem_nhds.mpr fun y hy ↦
      pathComponentIn_congr hy ▸ h y <| pathComponentIn_subset hy⟩

/-- Any topology coinduced by a locally path-connected topology is locally path-connected. -/
lemma LocPathConnectedSpace.coinduced {Y : Type*} (f : X → Y) :
    @LocPathConnectedSpace Y (.coinduced f ‹_›) := by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu ↦
    isOpen_coinduced.mpr <| isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refine mem_nhds_iff.mpr ⟨pathComponentIn (f ⁻¹' u) x, ?_,
    (hu.preimage hf).pathComponentIn _, mem_pathComponentIn_self hx'⟩
  rw [← image_subset_iff, ← pathComponentIn_congr hx]
  exact ((isPathConnected_pathComponentIn hx').image hf).subset_pathComponentIn
    ⟨x, mem_pathComponentIn_self hx', rfl⟩ <|
    (image_mono pathComponentIn_subset).trans <| u.image_preimage_subset f

/-- Quotients of locally path-connected spaces are locally path-connected. -/
lemma Topology.IsQuotientMap.locPathConnectedSpace {f : X → Y} (h : IsQuotientMap f) :
    LocPathConnectedSpace Y :=
  h.2 ▸ LocPathConnectedSpace.coinduced f

/-- Quotients of locally path-connected spaces are locally path-connected. -/
instance Quot.locPathConnectedSpace {r : X → X → Prop} : LocPathConnectedSpace (Quot r) :=
  isQuotientMap_quot_mk.locPathConnectedSpace

/-- Quotients of locally path-connected spaces are locally path-connected. -/
instance Quotient.locPathConnectedSpace {s : Setoid X} : LocPathConnectedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.locPathConnectedSpace

/-- Disjoint unions of locally path-connected spaces are locally path-connected. -/
instance Sum.locPathConnectedSpace.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [LocPathConnectedSpace Y] :
    LocPathConnectedSpace (X ⊕ Y) := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' (pathComponentIn (Sum.inl ⁻¹' u) x), ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inl
      · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inl _ <| (hu.preimage continuous_inl).pathComponentIn _
    · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
  · refine ⟨Sum.inr '' (pathComponentIn (Sum.inr ⁻¹' u) y), ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inr
      · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inr _ <| (hu.preimage continuous_inr).pathComponentIn _
    · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩

/-- Disjoint unions of locally path-connected spaces are locally path-connected. -/
instance Sigma.locPathConnectedSpace {X : ι → Type*}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → LocPathConnectedSpace (X i)] :
    LocPathConnectedSpace ((i : ι) × X i) := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' (pathComponentIn ((Sigma.mk x.1) ⁻¹' u) x.2), ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_sigmaMk
    · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩
    · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
  · exact isOpenMap_sigmaMk _ <| (hu.preimage continuous_sigmaMk).pathComponentIn _
  · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩

instance AlexandrovDiscrete.locPathConnectedSpace [AlexandrovDiscrete X] :
    LocPathConnectedSpace X := by
  apply LocPathConnectedSpace.of_bases nhds_basis_nhdsKer_singleton
  simp only [forall_const, IsPathConnected, mem_nhdsKer_singleton]
  intro x
  exists x, specializes_rfl
  intro y hy
  symm
  apply hy.joinedIn <;> rewrite [mem_nhdsKer_singleton] <;> [assumption; rfl]

end LocPathConnectedSpace
