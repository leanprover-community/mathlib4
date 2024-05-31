/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Order.Group.InjSurj

/-!
# Ordered instances on submodules
-/

namespace Submodule
variable {R M : Type*}

section OrderedMonoid
variable [Semiring R]

/-- A submodule of an `OrderedAddCommMonoid` is an `OrderedAddCommMonoid`. -/
instance toOrderedAddCommMonoid [OrderedAddCommMonoid M] [Module R M] (S : Submodule R M) :
    OrderedAddCommMonoid S :=
  Subtype.coe_injective.orderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_add_comm_monoid Submodule.toOrderedAddCommMonoid

/-- A submodule of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`. -/
instance toLinearOrderedAddCommMonoid [LinearOrderedAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommMonoid S :=
  Subtype.coe_injective.linearOrderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_add_comm_monoid Submodule.toLinearOrderedAddCommMonoid

/-- A submodule of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`. -/
instance toOrderedCancelAddCommMonoid [OrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : OrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.orderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_cancel_add_comm_monoid Submodule.toOrderedCancelAddCommMonoid

/-- A submodule of a `LinearOrderedCancelAddCommMonoid` is a
`LinearOrderedCancelAddCommMonoid`. -/
instance toLinearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.linearOrderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_cancel_add_comm_monoid Submodule.toLinearOrderedCancelAddCommMonoid

end OrderedMonoid

section OrderedGroup
variable [Ring R]

/-- A submodule of an `OrderedAddCommGroup` is an `OrderedAddCommGroup`. -/
instance toOrderedAddCommGroup [OrderedAddCommGroup M] [Module R M] (S : Submodule R M) :
    OrderedAddCommGroup S :=
  Subtype.coe_injective.orderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_ordered_add_comm_group Submodule.toOrderedAddCommGroup

/-- A submodule of a `LinearOrderedAddCommGroup` is a
`LinearOrderedAddCommGroup`. -/
instance toLinearOrderedAddCommGroup [LinearOrderedAddCommGroup M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommGroup S :=
  Subtype.coe_injective.linearOrderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
#align submodule.to_linear_ordered_add_comm_group Submodule.toLinearOrderedAddCommGroup

end OrderedGroup
