/-
Copyright (c) 2026 Diwen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Diwen Yu
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Order.Copy

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

variable (G) in
/-- `normalClosure` forms a Galois insertion with the coercion to subgroups. -/
@[to_additive /-- `normalClosure` forms a Galois insertion with the coercion to additive
subgroups. -/]
protected def gi :
    GaloisInsertion (fun H : Subgroup G ↦ ofSubgroup (Subgroup.normalClosure H))
      ((↑) : NormalSubgroup G → Subgroup G) where
  choice H _ := ofSubgroup (Subgroup.normalClosure H)
  gc _ _ := Subgroup.normalClosure_subset_iff.symm
  le_l_u _ := Subgroup.le_normalClosure
  choice_eq _ _ := rfl

@[to_additive]
instance : CompleteLattice (NormalSubgroup G) :=
  fast_instance% CompleteLattice.copy
    (GaloisInsertion.liftCompleteLattice (NormalSubgroup.gi G))
    _ rfl
    { toSubgroup := ⊤ } (toSubgroup_injective <| (Subgroup.normalClosure_eq_self _).symm)
    { toSubgroup := ⊥ } (toSubgroup_injective <| (Subgroup.normalClosure_eq_self _).symm)
    (fun H K ↦ { toSubgroup := H.toSubgroup ⊔ K.toSubgroup })
      (funext fun H ↦ funext fun K ↦
        toSubgroup_injective <| (Subgroup.normalClosure_eq_self _).symm)
    (fun H K ↦ { toSubgroup := H.toSubgroup ⊓ K.toSubgroup })
      (funext fun H ↦ funext fun K ↦
        toSubgroup_injective <| (Subgroup.normalClosure_eq_self _).symm)
    _ rfl
    _ rfl

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
theorem mem_toSubgroup_iff {H : NormalSubgroup G} {g : G} : g ∈ H.toSubgroup ↔ g ∈ H :=
  .rfl

end NormalSubgroup
