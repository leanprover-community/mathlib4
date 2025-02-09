/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Module.Submodule.Defs
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
    OrderedAddCommMonoid S := fast_instance%
  Subtype.coe_injective.orderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of a `LinearOrderedAddCommMonoid` is a `LinearOrderedAddCommMonoid`. -/
instance toLinearOrderedAddCommMonoid [LinearOrderedAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommMonoid S := fast_instance%
  Subtype.coe_injective.linearOrderedAddCommMonoid Subtype.val rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of an `OrderedCancelAddCommMonoid` is an `OrderedCancelAddCommMonoid`. -/
instance toOrderedCancelAddCommMonoid [OrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : OrderedCancelAddCommMonoid S := fast_instance%
  Subtype.coe_injective.orderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of a `LinearOrderedCancelAddCommMonoid` is a
`LinearOrderedCancelAddCommMonoid`. -/
instance toLinearOrderedCancelAddCommMonoid [LinearOrderedCancelAddCommMonoid M] [Module R M]
    (S : Submodule R M) : LinearOrderedCancelAddCommMonoid S := fast_instance%
  Subtype.coe_injective.linearOrderedCancelAddCommMonoid Subtype.val rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end OrderedMonoid

section OrderedGroup
variable [Ring R]

/-- A submodule of an `OrderedAddCommGroup` is an `OrderedAddCommGroup`. -/
instance toOrderedAddCommGroup [OrderedAddCommGroup M] [Module R M] (S : Submodule R M) :
    OrderedAddCommGroup S := fast_instance%
  Subtype.coe_injective.orderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of a `LinearOrderedAddCommGroup` is a
`LinearOrderedAddCommGroup`. -/
instance toLinearOrderedAddCommGroup [LinearOrderedAddCommGroup M] [Module R M]
    (S : Submodule R M) : LinearOrderedAddCommGroup S := fast_instance%
  Subtype.coe_injective.linearOrderedAddCommGroup Subtype.val rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end OrderedGroup

end Submodule
