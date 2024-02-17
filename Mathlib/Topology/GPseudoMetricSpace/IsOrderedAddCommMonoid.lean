import Mathlib.Algebra.Order.Monoid.Defs

class IsOrderedAddCommMonoid (α : Type*) [PartialOrder α] [AddCommMonoid α] where
  /- Adding a constant on the left does not change the order -/
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

class IsOrderedCancelAddCommMonoid
  (α :Type*) [PartialOrder α] [AddCommMonoid α] extends IsOrderedAddCommMonoid α where
  protected le_of_add_le_add_left : ∀ (a b c : α), a + b ≤ a + c → b ≤ c

instance (α : Type*) [h1: LinearOrder α] [h2: AddCommMonoid α] [h3:IsOrderedAddCommMonoid α] :
    LinearOrderedAddCommMonoid α := {
  h1,h2,h3 with }

instance (α : Type*) [h1:LinearOrder α] [h2:AddCommMonoid α] [h3:IsOrderedCancelAddCommMonoid α] :
    LinearOrderedCancelAddCommMonoid α := {
  h1,h2,h3 with }
