/-
Copyright (c) 2024 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
import Mathlib.Algebra.Order.Monoid.Defs

/-!
# IsOrderedAddCommMonoid mixin

this file defines a mixin class for combining kinds orderings and kinds of AddCommMonoid.
this allows for previously undefined combinations like combining CompleteLinearOrder and
AddCommMonoid, preventing the need for defining increasingly complex combinations of the two.

## Main Definitions:

- `IsOrderedAddCommMonoid α`: a mixin for `PartialOrder α` and a
`AddCommMonoid α` such that weak inequalities are maintained under adding constants.
- `IsOrderedCancelAddCommMonoid α`: mixin for `PartialOrder α` and a
`AddCommMonoid α` such that weak inequalities are maintained under both adding and
cancelling out the adding of constants.

Additional useful definitions:

- `instance LinearOrderedAddCommMonoid α`
given `IsOrderedAddCommMonoid α` and `LinearOrder α`
- `instance LinearOrderedCancelAddCommMonoid α`
given `IsOrderedCancelAddCommMonoid α` and `LinearOrder α`
-/

/--mixin for saying adding a constant does not change weak inequality-/
class IsOrderedAddCommMonoid (α : Type*) [PartialOrder α] [AddCommMonoid α] : Prop where
  /- Adding a constant on the left does not change the order -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

/--mixin for saying removing the adding of a constant does not change weak inequality-/
class IsOrderedCancelAddCommMonoid
  (α :Type*) [PartialOrder α] [AddCommMonoid α] extends IsOrderedAddCommMonoid α : Prop where
  /- Removing the adding of a constant on the left does not change the order-/
  protected le_of_add_le_add_left : ∀ (a b c : α), a + b ≤ a + c → b ≤ c

instance (α : Type*) [h1: LinearOrder α] [h2: AddCommMonoid α] [h3:IsOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid α := {
  h1,h2,h3 with }

instance (α : Type*) [h1:LinearOrder α] [h2:AddCommMonoid α] [h3:IsOrderedCancelAddCommMonoid α] :
    LinearOrderedCancelAddCommMonoid α := {
  h1,h2,h3 with }
