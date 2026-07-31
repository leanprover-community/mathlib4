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
  normal : toSubgroup.Normal := by infer_instance

/-- A normal additive subgroup of an arbitrary additive group. -/
@[ext]
structure NormalAddSubgroup (G : Type*) [AddGroup G] extends AddSubgroup G where
  normal : toAddSubgroup.Normal := by infer_instance

attribute [to_additive] NormalSubgroup

namespace NormalSubgroup

variable {G : Type*} [Group G]

@[to_additive]
theorem toSubgroup_injective : Function.Injective (NormalSubgroup.toSubgroup (G := G)) :=
  fun A B h ↦ NormalSubgroup.ext (by simp [h])

@[to_additive]
instance : SetLike (NormalSubgroup G) G where
  coe H := H.toSubgroup
  coe_injective _ _ h := toSubgroup_injective <| SetLike.ext' h

@[to_additive]
instance : PartialOrder (NormalSubgroup G) := .ofSetLike (NormalSubgroup G) G

@[to_additive]
instance : SubgroupClass (NormalSubgroup G) G where
  mul_mem := Subsemigroup.mul_mem' _
  one_mem H := H.one_mem'
  inv_mem := Subgroup.inv_mem' _

@[to_additive]
instance : Coe (NormalSubgroup G) (Subgroup G) where
  coe H := H.toSubgroup

@[to_additive]
instance (H : NormalSubgroup G) : H.toSubgroup.Normal := H.normal

/-- Bundle a subgroup carrying a normality instance. -/
@[to_additive /-- Bundle an additive subgroup carrying a normality instance. -/]
def ofSubgroup (H : Subgroup G) [H.Normal] : NormalSubgroup G :=
  { toSubgroup := H }

@[to_additive (attr := simp)]
theorem toSubgroup_ofSubgroup (H : Subgroup G) [H.Normal] :
    ((ofSubgroup H : NormalSubgroup G) : Subgroup G) = H :=
  rfl

@[to_additive]
instance : OrderTop (NormalSubgroup G) where
  top := { toSubgroup := ⊤ }
  le_top H := show H.toSubgroup ≤ ⊤ from le_top

@[to_additive]
instance : OrderBot (NormalSubgroup G) where
  bot := { toSubgroup := ⊥ }
  bot_le H := show (⊥ : Subgroup G) ≤ H.toSubgroup from bot_le

@[to_additive]
instance : SemilatticeSup (NormalSubgroup G) where
  sup H K := { toSubgroup := H.toSubgroup ⊔ K.toSubgroup }
  le_sup_left H K := show H.toSubgroup ≤ H.toSubgroup ⊔ K.toSubgroup from le_sup_left
  le_sup_right H K := show K.toSubgroup ≤ H.toSubgroup ⊔ K.toSubgroup from le_sup_right
  sup_le H K L hH hK :=
    show H.toSubgroup ⊔ K.toSubgroup ≤ L.toSubgroup from sup_le hH hK

@[to_additive]
instance : SemilatticeInf (NormalSubgroup G) where
  inf H K := { toSubgroup := H.toSubgroup ⊓ K.toSubgroup }
  inf_le_left H K := show H.toSubgroup ⊓ K.toSubgroup ≤ H.toSubgroup from inf_le_left
  inf_le_right H K := show H.toSubgroup ⊓ K.toSubgroup ≤ K.toSubgroup from inf_le_right
  le_inf H K L hK hL :=
    show H.toSubgroup ≤ K.toSubgroup ⊓ L.toSubgroup from le_inf hK hL

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
instance : CompleteLattice (NormalSubgroup G) where
  __ := (inferInstance : OrderTop (NormalSubgroup G))
  __ := (inferInstance : OrderBot (NormalSubgroup G))
  __ := (inferInstance : SemilatticeSup (NormalSubgroup G))
  __ := (inferInstance : SemilatticeInf (NormalSubgroup G))
  __ := (NormalSubgroup.gi G).liftCompleteLattice

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
