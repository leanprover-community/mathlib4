/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Order.Sublattice
import Mathlib.Order.Hom.CompleteLattice

/-!
# Complete Sublattices

This file defines complete sublattices. These are subsets of complete lattices which are closed
under arbitrary suprema and infima. As a standard example one could take the complete sublattice of
invariant submodules of some module with respect to a linear map.

## Main definitions:
  * `CompleteSublattice`: the definition of a complete sublattice
  * `CompleteSublattice.mk'`: an alternate constructor for a complete sublattice, demanding fewer
    hypotheses
  * `CompleteSublattice.instCompleteLattice`: a complete sublattice is a complete lattice
  * `CompleteSublattice.map`: complete sublattices push forward under complete lattice morphisms.
  * `CompleteSublattice.comap`: complete sublattices pull back under complete lattice morphisms.

-/

open Function Set

variable (α β : Type*) [CompleteLattice α] [CompleteLattice β] (f : CompleteLatticeHom α β)

/-- A complete sublattice is a subset of a complete lattice that is closed under arbitrary suprema
and infima. -/
structure CompleteSublattice extends Sublattice α where
  sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier
  sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier

variable {α β}

namespace CompleteSublattice

/-- To check that a subset is a complete sublattice, one does not need to check that it is closed
under binary `Sup` since this follows from the stronger `sSup` condition. Likewise for infima. -/
@[simps] def mk' (carrier : Set α)
    (sSupClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sSup s ∈ carrier)
    (sInfClosed' : ∀ ⦃s : Set α⦄, s ⊆ carrier → sInf s ∈ carrier) :
  CompleteSublattice α where
    carrier := carrier
    sSupClosed' := sSupClosed'
    sInfClosed' := sInfClosed'
    supClosed' := fun x hx y hy ↦ by
      suffices x ⊔ y = sSup {x, y} by exact this ▸ sSupClosed' (fun z hz ↦ by aesop)
      simp [sSup_singleton]
    infClosed' := fun x hx y hy ↦ by
      suffices x ⊓ y = sInf {x, y} by exact this ▸ sInfClosed' (fun z hz ↦ by aesop)
      simp [sInf_singleton]

variable {L : CompleteSublattice α}

instance instSetLike : SetLike (CompleteSublattice α) α where
  coe L := L.carrier
  coe_injective' L M h := by cases L; cases M; congr; exact SetLike.coe_injective' h

instance instBot : Bot L where
  bot := ⟨⊥, by simpa using L.sSupClosed' <| empty_subset _⟩

instance instTop : Top L where
  top := ⟨⊤, by simpa using L.sInfClosed' <| empty_subset _⟩

instance instSupSet : SupSet L where
  sSup s := ⟨sSup s, L.sSupClosed' image_val_subset⟩

instance instInfSet : InfSet L where
  sInf s := ⟨sInf s, L.sInfClosed' image_val_subset⟩

theorem sSupClosed {s : Set α} (h : s ⊆ L) : sSup s ∈ L := L.sSupClosed' h

theorem sInfClosed {s : Set α} (h : s ⊆ L) : sInf s ∈ L := L.sInfClosed' h

@[simp] theorem coe_bot : (↑(⊥ : L) : α) = ⊥ := rfl

@[simp] theorem coe_top : (↑(⊤ : L) : α) = ⊤ := rfl

@[simp] theorem coe_sSup (S : Set L) : (↑(sSup S) : α) = sSup {(s : α) | s ∈ S} := rfl

theorem coe_sSup' (S : Set L) : (↑(sSup S) : α) = ⨆ N ∈ S, (N : α) := by
  rw [coe_sSup, ← Set.image, sSup_image]

@[simp] theorem coe_sInf (S : Set L) : (↑(sInf S) : α) = sInf {(s : α) | s ∈ S} := rfl

theorem coe_sInf' (S : Set L) : (↑(sInf S) : α) = ⨅ N ∈ S, (N : α) := by
  rw [coe_sInf, ← Set.image, sInf_image]

instance instCompleteLattice : CompleteLattice L :=
  Subtype.coe_injective.completeLattice _
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

/-- The push forward of a complete sublattice under a complete lattice hom is a complete
sublattice. -/
@[simps] def map (L : CompleteSublattice α) : CompleteSublattice β where
  carrier := f '' L
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
  sSupClosed' := fun s hs ↦ by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sSup]
    exact mem_image_of_mem f (sSupClosed ht)
  sInfClosed' := fun s hs ↦ by
    obtain ⟨t, ht, rfl⟩ := subset_image_iff.mp hs
    rw [← map_sInf]
    exact mem_image_of_mem f (sInfClosed ht)

@[simp] theorem mem_map {b : β} : b ∈ L.map f ↔ ∃ a ∈ L, f a = b := Iff.rfl

/-- The pull back of a complete sublattice under a complete lattice hom is a complete sublattice. -/
@[simps] def comap (L : CompleteSublattice β) : CompleteSublattice α where
  carrier := f ⁻¹' L
  supClosed' := L.supClosed.preimage f
  infClosed' := L.infClosed.preimage f
  sSupClosed' s hs := by
    simpa only [mem_preimage, map_sSup, SetLike.mem_coe] using sSupClosed <| mapsTo'.mp hs
  sInfClosed' s hs := by
    simpa only [mem_preimage, map_sInf, SetLike.mem_coe] using sInfClosed <| mapsTo'.mp hs

@[simp] theorem mem_comap {L : CompleteSublattice β} {a : α} : a ∈ L.comap f ↔ f a ∈ L := Iff.rfl

end CompleteSublattice
