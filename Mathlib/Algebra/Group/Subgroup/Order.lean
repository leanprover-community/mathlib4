/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Order.Group.InjSurj
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Ordered instances on subgroups
-/

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
