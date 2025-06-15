/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Set.Functor
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
  sSup s := ⟨sSup <| (↑) '' s, L.sSupClosed' image_val_subset⟩

instance instInfSet : InfSet L where
  sInf s := ⟨sInf <| (↑) '' s, L.sInfClosed' image_val_subset⟩

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

-- Redeclaring to get proper keys for these instances
instance : Max {x // x ∈ L} := Sublattice.instSupCoe
instance : Min {x // x ∈ L} := Sublattice.instInfCoe

instance instCompleteLattice : CompleteLattice L :=
  Subtype.coe_injective.completeLattice _
    Sublattice.coe_sup Sublattice.coe_inf coe_sSup' coe_sInf' coe_top coe_bot

/-- The natural complete lattice hom from a complete sublattice to the original lattice. -/
def subtype (L : CompleteSublattice α) : CompleteLatticeHom L α where
  toFun := Subtype.val
  map_sInf' _ := rfl
  map_sSup' _ := rfl

@[simp, norm_cast] lemma coe_subtype (L : CompleteSublattice α) : L.subtype = ((↑) : L → α) := rfl
lemma subtype_apply (L : Sublattice α) (a : L) : L.subtype a = a := rfl

lemma subtype_injective (L : CompleteSublattice α) :
    Injective <| subtype L := Subtype.coe_injective

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

protected lemma disjoint_iff {a b : L} :
    Disjoint a b ↔ Disjoint (a : α) (b : α) := by
  rw [disjoint_iff, disjoint_iff, ← Sublattice.coe_inf, ← coe_bot (L := L),
    Subtype.coe_injective.eq_iff]

protected lemma codisjoint_iff {a b : L} :
    Codisjoint a b ↔ Codisjoint (a : α) (b : α) := by
  rw [codisjoint_iff, codisjoint_iff, ← Sublattice.coe_sup, ← coe_top (L := L),
    Subtype.coe_injective.eq_iff]

protected lemma isCompl_iff {a b : L} :
    IsCompl a b ↔ IsCompl (a : α) (b : α) := by
  rw [isCompl_iff, isCompl_iff, CompleteSublattice.disjoint_iff, CompleteSublattice.codisjoint_iff]

lemma isComplemented_iff : ComplementedLattice L ↔ ∀ a ∈ L, ∃ b ∈ L, IsCompl a b := by
  refine ⟨fun ⟨h⟩ a ha ↦ ?_, fun h ↦ ⟨fun ⟨a, ha⟩ ↦ ?_⟩⟩
  · obtain ⟨b, hb⟩ := h ⟨a, ha⟩
    exact ⟨b, b.property, CompleteSublattice.isCompl_iff.mp hb⟩
  · obtain ⟨b, hb, hb'⟩ := h a ha
    exact ⟨⟨b, hb⟩, CompleteSublattice.isCompl_iff.mpr hb'⟩

instance : Top (CompleteSublattice α) := ⟨mk' univ (fun _ _ ↦ mem_univ _) (fun _ _ ↦ mem_univ _)⟩

variable (L)

/-- Copy of a complete sublattice with a new `carrier` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (s : Set α) (hs : s = L) : CompleteSublattice α :=
  mk' s (hs ▸ L.sSupClosed') (hs ▸ L.sInfClosed')

@[simp, norm_cast] lemma coe_copy (s : Set α) (hs) : L.copy s hs = s := rfl

lemma copy_eq (s : Set α) (hs) : L.copy s hs = L := SetLike.coe_injective hs

end CompleteSublattice

namespace CompleteLatticeHom

/-- The range of a `CompleteLatticeHom` is a `CompleteSublattice`.

See Note [range copy pattern]. -/
protected def range : CompleteSublattice β :=
  (CompleteSublattice.map f ⊤).copy (range f) image_univ.symm

theorem range_coe : (f.range : Set β) = range f := rfl

/-- We can regard a complete lattice homomorphism as an order equivalence to its range. -/
@[simps! apply] noncomputable def toOrderIsoRangeOfInjective (hf : Injective f) : α ≃o f.range :=
  (orderEmbeddingOfInjective f hf).orderIso

end CompleteLatticeHom
