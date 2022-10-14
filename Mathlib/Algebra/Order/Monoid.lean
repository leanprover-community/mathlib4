import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.CovariantAndContravariant
import Mathlib.Algebra.Order.MonoidLemmas

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
class OrderedCommMonoid (α : Type _) extends CommMonoid α, PartialOrder α where
  protected mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
class OrderedAddCommMonoid (α : Type _) extends AddCommMonoid α, PartialOrder α where
  protected add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

attribute [to_additive OrderedAddCommMonoid] OrderedCommMonoid

section OrderedInstances
open Function

@[to_additive OrderedAddCommMonoid.to_covariant_class_left]
instance OrderedCommMonoid.to_covariant_class_left (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (· * ·) (· ≤ ·) where
  elim := fun a _ _ bc => OrderedCommMonoid.mul_le_mul_left _ _ bc a

-- TODO `to_additive` should copy this
attribute [instance] OrderedAddCommMonoid.to_covariant_class_left

/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive OrderedAddCommMonoid.to_covariant_class_right]
instance OrderedCommMonoid.to_covariant_class_right (M : Type _) [OrderedCommMonoid M] :
    CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  covariant_swap_mul_le_of_covariant_mul_le M

-- TODO `to_additive` should copy this
attribute [instance] OrderedAddCommMonoid.to_covariant_class_right

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)` implies
`covariant_class M M (*) (<)`, see `left_cancel_semigroup.covariant_mul_lt_of_covariant_mul_le`. -/
@[to_additive Add.to_covariant_class_left]
theorem Mul.to_covariant_class_left (M : Type _) [Mul M] [PartialOrder M]
    [CovariantClass M M (· * ·) (· < ·)] : CovariantClass M M (· * ·) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

-- TODO `to_additive` should copy this
attribute [instance] Add.to_covariant_class_left

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)`, see
`right_cancel_semigroup.covariant_swap_mul_lt_of_covariant_swap_mul_le`. -/
@[to_additive Add.to_covariant_class_right]
theorem Mul.to_covariant_class_right (M : Type _) [Mul M] [PartialOrder M]
    [CovariantClass M M (swap (· * ·)) (· < ·)] : CovariantClass M M (swap (· * ·)) (· ≤ ·) :=
  ⟨covariant_le_of_covariant_lt _ _ _ CovariantClass.elim⟩

-- TODO `to_additive` should copy this
attribute [instance] Add.to_covariant_class_right

end OrderedInstances

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
class OrderedCancelAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[to_additive OrderedCancelAddCommMonoid]
class OrderedCancelCommMonoid (α : Type u) extends CommMonoid α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c


-- see Note [lower instance priority]
@[to_additive OrderedCancelAddCommMonoid.toOrderedAddCommMonoid]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid [OrderedCancelCommMonoid α] :
    OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }

-- TODO `to_additive` should copy this
attribute [instance] OrderedCancelAddCommMonoid.toOrderedAddCommMonoid
