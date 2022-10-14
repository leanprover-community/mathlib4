import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Order.Monoid
import Mathlib.Algebra.Order.MonoidLemmas

open Function

/-- An ordered additive commutative group is an additive commutative group
with a partial order in which addition is strictly monotone. -/
class OrderedAddCommGroup (α : Type u) extends AddCommGroup α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b

/-- An ordered commutative group is an commutative group
with a partial order in which multiplication is strictly monotone. -/
class OrderedCommGroup (α : Type u) extends CommGroup α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b

attribute [to_additive OrderedAddCommGroup] OrderedCommGroup

@[to_additive]
instance OrderedCommGroup.to_covariant_class_left_le [OrderedCommGroup α] :
    CovariantClass α α (· * ·) (· ≤ ·) where
  elim := fun a b c bc => OrderedCommGroup.mul_le_mul_left b c bc a

-- see Note [lower instance priority]
@[to_additive OrderedAddCommGroup.toOrderedCancelAddCommMonoid]
instance (priority := 100) OrderedCommGroup.toOrderedCancelCommMonoid [s : OrderedCommGroup α] :
    OrderedCancelCommMonoid α :=
  { s with le_of_mul_le_mul_left := fun a _ _ => (mul_le_mul_iff_left a).mp }

attribute [instance] OrderedAddCommGroup.toOrderedCancelAddCommMonoid

section Group
variable [Group α] [LT α]

section TypeclassesLeftLt

variable [CovariantClass α α (· * ·) (· < ·)] {a b c : α}

/-- Uses `Left` co(ntra)variant. -/
@[simp, to_additive Left.neg_pos_iff "Uses `Left` co(ntra)variant."]
theorem Left.one_lt_inv_iff : 1 < a⁻¹ ↔ a < 1 := by
  rw [← mul_lt_mul_iff_left a, mul_inv_self, mul_one]

end TypeclassesLeftLt

section Right

variable [CovariantClass α α (swap (· * ·)) (· < ·)] {a b c d : α}

-- FIXME: restore @[to_additive sub_pos]
@[simp]
theorem one_lt_div' : 1 < a / b ↔ b < a := by
  rw [← mul_lt_mul_iff_right b, one_mul, div_eq_mul_inv, inv_mul_cancel_right]

end Right

end Group

alias Left.one_lt_inv_iff ↔ _ one_lt_inv_of_inv
attribute [to_additive neg_pos_of_neg] one_lt_inv_of_inv

/-!
### Linearly ordered commutative groups
-/


/-- A linearly ordered additive commutative group is an
additive commutative group with a linear order in which
addition is monotone. -/
class LinearOrderedAddCommGroup (α : Type u) extends OrderedAddCommGroup α, LinearOrder α
