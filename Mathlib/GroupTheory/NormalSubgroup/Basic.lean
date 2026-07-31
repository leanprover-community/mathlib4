/-
Copyright (c) 2026 Diwen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diwen Yu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Normal subgroups as a complete lattice

This file bundles normal subgroups of an arbitrary group and equips them with the complete lattice
structure inherited from `Subgroup`.
-/

@[expose] public section

/-- A normal subgroup of an arbitrary group. -/
@[ext]
structure NormalSubgroup (G : Type*) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance

/-- A normal additive subgroup of an arbitrary additive group. -/
@[ext]
structure NormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup G where
  isNormal' : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] NormalSubgroup

namespace NormalSubgroup

variable {G : Type*} [Group G]

@[to_additive]
theorem toSubgroup_injective : Function.Injective
    (fun H ↦ H.toSubgroup : NormalSubgroup G → Subgroup G) :=
  fun A B h ↦ by
    ext
    dsimp at h
    rw [h]

@[to_additive]
instance : SetLike (NormalSubgroup G) G where
  coe H := H.toSubgroup
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : PartialOrder (NormalSubgroup G) := .ofSetLike (NormalSubgroup G) G

@[to_additive]
instance : SubgroupClass (NormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem H := H.toSubgroup.one_mem
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (NormalSubgroup G) (Subgroup G) where
  coe H := H.toSubgroup

@[to_additive]
instance (H : NormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

/-- Bundle a subgroup carrying a normality instance. -/
@[to_additive /-- Bundle an additive subgroup carrying a normality instance. -/]
def ofSubgroup (H : Subgroup G) [H.Normal] : NormalSubgroup G :=
  { toSubgroup := H }

@[to_additive (attr := simp)]
theorem toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] :
    ((ofSubgroup H : NormalSubgroup G) : Subgroup G) = H :=
  rfl

@[to_additive]
instance : Top (NormalSubgroup G) :=
  ⟨{ toSubgroup := ⊤ }⟩

@[to_additive]
instance : Bot (NormalSubgroup G) :=
  ⟨{ toSubgroup := ⊥ }⟩

@[to_additive]
instance : Max (NormalSubgroup G) :=
  ⟨fun H K ↦ { toSubgroup := H.toSubgroup ⊔ K.toSubgroup }⟩

@[to_additive]
instance : Min (NormalSubgroup G) :=
  ⟨fun H K ↦ { toSubgroup := H.toSubgroup ⊓ K.toSubgroup }⟩

@[to_additive]
instance : SupSet (NormalSubgroup G) :=
  ⟨fun s ↦ { toSubgroup := ⨆ H, ⨆ (_ : H ∈ s), H.toSubgroup }⟩

@[to_additive]
instance : InfSet (NormalSubgroup G) :=
  ⟨fun s ↦ {
    toSubgroup := ⨅ H, ⨅ (_ : H ∈ s), H.toSubgroup
    isNormal' := Subgroup.normal_iInf_normal fun H ↦
      Subgroup.normal_iInf_normal fun _ ↦ H.isNormal'
  }⟩

@[to_additive (attr := simp)]
theorem toSubgroup_top : ((⊤ : NormalSubgroup G) : Subgroup G) = ⊤ := rfl

@[to_additive (attr := simp)]
theorem toSubgroup_bot : ((⊥ : NormalSubgroup G) : Subgroup G) = ⊥ := rfl

@[to_additive (attr := simp)]
theorem toSubgroup_sup (H K : NormalSubgroup G) :
    ((H ⊔ K : NormalSubgroup G) : Subgroup G) = H.toSubgroup ⊔ K.toSubgroup :=
  rfl

@[to_additive (attr := simp)]
theorem toSubgroup_inf (H K : NormalSubgroup G) :
    ((H ⊓ K : NormalSubgroup G) : Subgroup G) = H.toSubgroup ⊓ K.toSubgroup :=
  rfl

@[to_additive (attr := simp)]
theorem toSubgroup_sSup (s : Set (NormalSubgroup G)) :
    ((sSup s : NormalSubgroup G) : Subgroup G) = ⨆ H, ⨆ (_ : H ∈ s), H.toSubgroup :=
  rfl

@[to_additive (attr := simp)]
theorem toSubgroup_sInf (s : Set (NormalSubgroup G)) :
    ((sInf s : NormalSubgroup G) : Subgroup G) = ⨅ H, ⨅ (_ : H ∈ s), H.toSubgroup :=
  rfl

@[to_additive]
instance : CompleteLattice (NormalSubgroup G) :=
  toSubgroup_injective.completeLattice _ .rfl .rfl toSubgroup_sup toSubgroup_inf
    toSubgroup_sSup toSubgroup_sInf toSubgroup_top toSubgroup_bot

@[to_additive (attr := simp)]
theorem mem_toSubgroup_iff {H : NormalSubgroup G} {g : G} : g ∈ H.toSubgroup ↔ g ∈ H :=
  .rfl

end NormalSubgroup
