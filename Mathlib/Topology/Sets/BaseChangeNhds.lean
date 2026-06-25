/-
Copyright (c) 2026 Yannis Monbru-Carcelero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yannis Monbru Carcelero
-/

module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Sets.Compacts

/-!
# Base changes among different families of neighbourhoods

This file builds base changes for `.compactInsd`, `openNhds`.

It also contains the evidences that `oRcNhds_to_openNhds`and
 `oRcNhds_to_compactNhds` are initials functors.

-/

@[expose] public section

namespace TopologicalSpace

open Set CategoryTheory Limits

variable {α : Type*} [TopologicalSpace α]

namespace Opens

/-- For U an open subset included in a open subset V, there is
a map sending compacts inside U to the ones inside V -/
def baseChangeCompactInsd {U V : Opens α} (h : U ⟶ V) : U.compactInsd → V.compactInsd :=
  fun ⟨K,hK⟩ ↦ ⟨K, fun _ hx ↦ Set.mem_of_subset_of_mem (leOfHom h) (hK hx)⟩

lemma monoBaseChangeCompactInsd {U V : Opens α} (h : U ⟶ V) : Monotone <| baseChangeCompactInsd h :=
  fun _ _ hKL _ hx ↦ SetLike.mem_coe.mpr (hKL hx)

end Opens

namespace Compacts

/-- For K a compact subset included in a compact subset L, there
is a map sending open neighbourhoods of L to the ones of K -/
def baseChangeOpenNhds {K L : Compacts α} (h : K ⟶ L) : L.openNhds → K.openNhds :=
  fun ⟨U,hU⟩ ↦ ⟨U, fun _ hx ↦ Set.mem_of_subset_of_mem hU (leOfHom h hx)⟩

lemma monoBaseChangeOpenNhds {K L : Compacts α} (h : K ⟶ L) : Monotone <| baseChangeOpenNhds h :=
  fun _ _ hUV _ hx ↦ SetLike.mem_coe.mpr (hUV hx)

@[simp]
lemma baseChangeOpenNhds_comp {K L M : Compacts α} (h : K ⟶ L) (k : L ⟶ M) (U : M.openNhds) :
  baseChangeOpenNhds (h ≫ k) U = baseChangeOpenNhds h (baseChangeOpenNhds k U) := by rfl

/-- The evidence that ⊥ is initial among the open Nhds of ⊥ -/
def isInitialElemOpensOpenNhdsBot : IsInitial (⊥ : (⊥ : Compacts α).openNhds) := .ofUniqueHom
  (fun _ ↦ homOfLE <| by tauto)
  (fun _ _ ↦ eq_of_comp_right_eq <| by tauto)

instance {K : Compacts α} [T2Space α] [LocallyCompactSpace α] :
    K.mono_oRcNhds_to_openNhds.functor.Initial := by
  apply (Monotone.initial_functor_iff _).2
  intro U
  obtain ⟨L, h1, h2, h3⟩ := exists_compact_between K.isCompact U.val.isOpen U.property
  use ⟨⟨interior L, isOpen_interior⟩,
    ⟨IsCompact.of_isClosed_subset h1 isClosed_closure
      (closure_minimal interior_subset (IsCompact.isClosed h1)),
    h2⟩⟩
  exact Subset.trans interior_subset h3

instance {K : Compacts α} [T2Space α] : K.mono_oRcNhds_to_compactNhds.functor.Initial := by
  apply (Monotone.initial_functor_iff _).2
  intro L
  obtain ⟨U, h1, h2⟩ := exists_open_nhds_sub_compact_nhds L
  have h3 : closure (U : Set α) ⊆ L := (IsClosed.closure_subset_iff
    (IsCompact.isClosed L.1.isCompact') ).2 h2
  exact ⟨⟨U, ⟨ IsCompact.of_isClosed_subset L.1.isCompact' isClosed_closure h3, h1⟩⟩, h3⟩

variable {β : Type u_1} [TopologicalSpace β] {f : α → β} (pf : IsProperMap f)

/--
The preimage of a compact by a proper map as a compact -/
@[simps]
def properPreimage (K : Compacts β) : Compacts α :=
  ⟨f ⁻¹' K.carrier , IsProperMap.isCompact_preimage pf K.isCompact'⟩

lemma properPreimage_mono : Monotone (properPreimage pf) := fun _ _ h ↦ by
  apply SetLike.coe_subset_coe.1
  simp only [coe_properPreimage, Compacts.carrier_eq_coe]
  exact Set.preimage_mono h
  -- show_term donne SetLike.coe_subset_coe.mp (id (preimage_mono h)) et ça ne marche pas

/--
The base change of compactNhds induced by properPreimage -/
@[simps]
def nhdsMap (K : Compacts β) (L : K.compactNhds) : (properPreimage pf K).compactNhds :=
  ⟨properPreimage pf L,
  by
    obtain ⟨U,hU1,hU2⟩ := exists_open_nhds_sub_compact_nhds L
    refine (compactNhdsOfExistsOpenSubsetBetween _ ?_ ?_ ?_).property
    · exact ((Opens.map (TopCat.ofHom ( ContinuousMap.mk f pf.toContinuous))).obj U)
    · simp only [coe_properPreimage]
      exact Set.preimage_mono hU1-- pareil que dans properMap_mono avec showtrem
    · simp only [coe_mk]
      exact Set.preimage_mono hU2
      ⟩

lemma nhdsMap_mono (K : Compacts β) : Monotone (nhdsMap pf K) :=
  fun _ _ h ↦ properPreimage_mono pf h

--trouver meilleure endroit
lemma IsClosedMap.isOpen_kernImage {f : α → β} (closed_f : IsClosedMap f) {u : Set α}
    (hu : IsOpen u) : IsOpen (kernImage f u) := by
  rw [Set.kernImage_eq_compl]
  exact (closed_f _ hu.isClosed_compl).isOpen_compl

instance [T2Space β] [LocallyCompactSpace β] (K : Compacts β) : (nhdsMap_mono pf K).functor.Initial
    := by
  apply (Monotone.initial_functor_iff _).2
  intro L
  obtain ⟨U,hU1,hU2⟩ := exists_open_nhds_sub_compact_nhds L
  obtain ⟨M,hM1,hM2,hM3⟩ :=
    exists_compact_between K.isCompact'
    (IsClosedMap.isOpen_kernImage (IsProperMap.isClosedMap pf) U.isOpen)
    (Set.subset_kernImage_iff.2 hU1)
  use ⟨⟨M,hM1⟩,
    (compactNhdsOfExistsOpenSubsetBetween _ ⟨interior M, isOpen_interior⟩
    hM2 interior_subset).property⟩
  exact (Set.subset_kernImage_iff.1 hM3).trans hU2

end Compacts

end TopologicalSpace
