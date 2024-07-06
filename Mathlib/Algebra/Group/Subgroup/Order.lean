/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Ruben Van de Velde
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.InjSurj
import Mathlib.Order.Atoms

/-!
# Facts about ordered structures and ordered instances on subgroups
-/

open Subgroup

@[simp] theorem abs_mem_iff {S G} [AddGroup G] [LinearOrder G] {_ : SetLike S G}
    [NegMemClass S G] {H : S} {x : G} : |x| ∈ H ↔ x ∈ H := by
  cases abs_choice x <;> simp [*]

section ModularLattice

variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}

@[to_additive]
instance : IsModularLattice (Subgroup C) :=
  ⟨fun {x} y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end ModularLattice

section Coatom
namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/-- In a group that satisfies the normalizer condition, every maximal subgroup is normal -/
theorem NormalizerCondition.normal_of_coatom (hnc : NormalizerCondition G) (hmax : IsCoatom H) :
    H.Normal :=
  normalizer_eq_top.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))
#align subgroup.normalizer_condition.normal_of_coatom Subgroup.NormalizerCondition.normal_of_coatom

@[simp]
theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]
theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.mapSubgroup) K

lemma isCoatom_comap_of_surjective
    {H : Type*} [Group H] {φ : G →* H} (hφ : Function.Surjective φ)
    {M : Subgroup H} (hM : IsCoatom M) : IsCoatom (M.comap φ) := by
  refine And.imp (fun hM ↦ ?_) (fun hM ↦ ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ, ← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le), comap_top] at hM
    exact hM hK

end Subgroup
end Coatom

namespace SubgroupClass
variable {G S : Type*} [SetLike S G]

-- Prefer subclasses of `Group` over subclasses of `SubgroupClass`.
/-- A subgroup of an `OrderedCommGroup` is an `OrderedCommGroup`. -/
@[to_additive "An additive subgroup of an `AddOrderedCommGroup` is an `AddOrderedCommGroup`."]
instance (priority := 75) toOrderedCommGroup [OrderedCommGroup G]
    [SubgroupClass S G] (H : S) : OrderedCommGroup H :=
  Subtype.coe_injective.orderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align subgroup_class.to_ordered_comm_group SubgroupClass.toOrderedCommGroup
#align add_subgroup_class.to_ordered_add_comm_group AddSubgroupClass.toOrderedAddCommGroup

-- Prefer subclasses of `Group` over subclasses of `SubgroupClass`.
/-- A subgroup of a `LinearOrderedCommGroup` is a `LinearOrderedCommGroup`. -/
@[to_additive
      "An additive subgroup of a `LinearOrderedAddCommGroup` is a
        `LinearOrderedAddCommGroup`."]
instance (priority := 75) toLinearOrderedCommGroup [LinearOrderedCommGroup G]
    [SubgroupClass S G] (H : S) : LinearOrderedCommGroup H :=
  Subtype.coe_injective.linearOrderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subgroup_class.to_linear_ordered_comm_group SubgroupClass.toLinearOrderedCommGroup
#align add_subgroup_class.to_linear_ordered_add_comm_group AddSubgroupClass.toLinearOrderedAddCommGroup

end SubgroupClass

namespace Subgroup

variable {G : Type*}

/-- A subgroup of an `OrderedCommGroup` is an `OrderedCommGroup`. -/
@[to_additive "An `AddSubgroup` of an `AddOrderedCommGroup` is an `AddOrderedCommGroup`."]
instance toOrderedCommGroup [OrderedCommGroup G] (H : Subgroup G) :
    OrderedCommGroup H :=
  Subtype.coe_injective.orderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align subgroup.to_ordered_comm_group Subgroup.toOrderedCommGroup
#align add_subgroup.to_ordered_add_comm_group AddSubgroup.toOrderedAddCommGroup

/-- A subgroup of a `LinearOrderedCommGroup` is a `LinearOrderedCommGroup`. -/
@[to_additive
      "An `AddSubgroup` of a `LinearOrderedAddCommGroup` is a
        `LinearOrderedAddCommGroup`."]
instance toLinearOrderedCommGroup [LinearOrderedCommGroup G] (H : Subgroup G) :
    LinearOrderedCommGroup H :=
  Subtype.coe_injective.linearOrderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align subgroup.to_linear_ordered_comm_group Subgroup.toLinearOrderedCommGroup
#align add_subgroup.to_linear_ordered_add_comm_group AddSubgroup.toLinearOrderedAddCommGroup

end Subgroup
