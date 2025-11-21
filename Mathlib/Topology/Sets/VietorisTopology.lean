/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Sets.Compacts

/-!
# Vietoris topology

This file defines the Vietoris topology on the types of compact subsets and nonempty compact subsets
of a topological space.
-/

@[expose] public section

open Set Topology

variable (α : Type*) [TopologicalSpace α]

namespace TopologicalSpace

/-- The Vietoris topology on the powerset of a topological space. Used for defining the topologies
on `Compacts` and `NonemptyCompacts`. -/
protected def vietoris : TopologicalSpace (Set α) :=
  .generateFrom <| powerset '' {U | IsOpen U} ∪ (fun V => {s | (s ∩ V).Nonempty}) '' {V | IsOpen V}

attribute [local instance] TopologicalSpace.vietoris

variable {α}

namespace vietoris

theorem isOpen_powerset {U : Set α} (h : IsOpen U) :
    IsOpen U.powerset :=
  isOpen_generateFrom_of_mem <| .inl ⟨U, h, rfl⟩

theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (h : IsOpen U) :
    IsOpen {s | (s ∩ U).Nonempty} :=
  isOpen_generateFrom_of_mem <| .inr ⟨U, h, rfl⟩

theorem isClosed_powerset {F : Set α} (h : IsClosed F) :
    IsClosed F.powerset := by
  simp_rw [powerset, ← isOpen_compl_iff, compl_setOf, ← inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen h.isOpen_compl

theorem isClosed_inter_nonempty_of_isClosed {F : Set α} (h : IsClosed F) :
    IsClosed {s | (s ∩ F).Nonempty} := by
  simp_rw +singlePass [← compl_compl F, inter_compl_nonempty_iff, ← compl_setOf]
  exact (isOpen_powerset h.isOpen_compl).isClosed_compl

theorem isClopen_singleton_empty : IsClopen {(∅ : Set α)} := by
  rw [← powerset_empty]
  exact ⟨isClosed_powerset isClosed_empty, isOpen_powerset isOpen_empty⟩

end vietoris

namespace Compacts

/-- The Vietoris topology on the compact subsets of a topological space. -/
instance topology : TopologicalSpace (Compacts α) :=
  .induced (↑) (.vietoris α)

@[fun_prop]
theorem isEmbedding_coe : IsEmbedding ((↑) : Compacts α → Set α) where
  injective := SetLike.coe_injective
  eq_induced := rfl

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : Compacts α → Set α) :=
  isEmbedding_coe.continuous

theorem isOpen_subsets_of_isOpen {U : Set α} (h : IsOpen U) :
    IsOpen {K : Compacts α | (K : Set α) ⊆ U} :=
  continuous_coe.isOpen_preimage _ <| vietoris.isOpen_powerset h

theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (h : IsOpen U) :
    IsOpen {K : Compacts α | ((K : Set α) ∩ U).Nonempty} :=
  continuous_coe.isOpen_preimage _ <| vietoris.isOpen_inter_nonempty_of_isOpen h

theorem isClosed_subsets_of_isClosed {F : Set α} (h : IsClosed F) :
    IsClosed {K : Compacts α | (K : Set α) ⊆ F} := by
  simp_rw [← isOpen_compl_iff, Set.compl_setOf, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen h.isOpen_compl

theorem isClosed_inter_nonempty_of_isClosed {F : Set α} (h : IsClosed F) :
    IsClosed {K : Compacts α | ((K : Set α) ∩ F).Nonempty} := by
  simp_rw +singlePass [← compl_compl F, Set.inter_compl_nonempty_iff, ← Set.compl_setOf]
  exact (isOpen_subsets_of_isOpen h.isOpen_compl).isClosed_compl

theorem isClopen_singleton_bot : IsClopen {(⊥ : Compacts α)} := by
  convert vietoris.isClopen_singleton_empty.preimage continuous_coe
  rw [← coe_bot, ← image_singleton (f := SetLike.coe), SetLike.coe_injective.preimage_image]

end Compacts

namespace NonemptyCompacts

/-- The Vietoris topology on the nonempty compact subsets of a topological space. -/
instance topology : TopologicalSpace (NonemptyCompacts α) :=
  .induced (↑) (.vietoris α)

@[fun_prop]
theorem isEmbedding_coe : IsEmbedding ((↑) : NonemptyCompacts α → Set α) where
  injective := SetLike.coe_injective
  eq_induced := rfl

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : NonemptyCompacts α → Set α) :=
  isEmbedding_coe.continuous

@[fun_prop]
theorem isEmbedding_toCompacts : IsEmbedding (toCompacts (α := α)) where
  injective := toCompacts_injective
  eq_induced := .symm <| induced_compose (f := toCompacts) (g := SetLike.coe)

@[fun_prop]
theorem continuous_toCompacts : Continuous (toCompacts (α := α)) :=
  isEmbedding_toCompacts.continuous

@[fun_prop]
theorem isClosedEmbedding_toCompacts : IsClosedEmbedding (toCompacts (α := α)) where
  __ := isEmbedding_toCompacts
  isClosed_range := by
    rw [range_toCompacts]
    exact Compacts.isClopen_singleton_bot.compl.isClosed

@[fun_prop]
theorem isOpenEmbedding_toCompacts : IsOpenEmbedding (toCompacts (α := α)) where
  __ := isEmbedding_toCompacts
  isOpen_range := by
    rw [range_toCompacts]
    exact Compacts.isClopen_singleton_bot.compl.isOpen

theorem isOpen_subsets_of_isOpen {U : Set α} (h : IsOpen U) :
    IsOpen {K : NonemptyCompacts α | (K : Set α) ⊆ U} :=
  (vietoris.isOpen_powerset h).preimage continuous_coe

theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (h : IsOpen U) :
    IsOpen {K : NonemptyCompacts α | ((K : Set α) ∩ U).Nonempty} :=
  (vietoris.isOpen_inter_nonempty_of_isOpen h).preimage continuous_coe

theorem isClosed_subsets_of_isClosed {F : Set α} (h : IsClosed F) :
    IsClosed {K : NonemptyCompacts α | (K : Set α) ⊆ F} :=
  (vietoris.isClosed_powerset h).preimage continuous_coe

theorem isClosed_inter_nonempty_of_isClosed {F : Set α} (h : IsClosed F) :
    IsClosed {K : NonemptyCompacts α | ((K : Set α) ∩ F).Nonempty} :=
  (vietoris.isClosed_inter_nonempty_of_isClosed h).preimage continuous_coe

end NonemptyCompacts

end TopologicalSpace
