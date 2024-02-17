import Mathlib.Algebra.Order.Monoid.Defs

class IsOrderedAddCommMonoid (α : Type*) [PartialOrder α] [AddCommMonoid α] where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c, c + a ≤ c + b

instance (α : Type*) [h1: LinearOrder α] [h2: AddCommMonoid α] [h3:IsOrderedAddCommMonoid α]:
  LinearOrderedAddCommMonoid α := {
  h1,h2,h3 with
}
