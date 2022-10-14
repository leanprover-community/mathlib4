import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Monoid
import Mathlib.Algebra.Order.Group

/-- An `OrderedSemiring α` is a semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedSemiring (α : Type u) extends Semiring α, OrderedCancelAddCommMonoid α where
  zero_le_one : (0 : α) ≤ 1
  mul_lt_mul_of_pos_left : ∀ a b c : α, a < b → 0 < c → c * a < c * b
  mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c

/-- An `OrderedRing α` is a ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
class OrderedRing (α : Type u) extends Ring α, OrderedAddCommGroup α where
  zero_le_one : 0 ≤ (1 : α)
  mul_pos : ∀ a b : α, 0 < a → 0 < b → 0 < a * b

-- section OrderedRing

-- variable [OrderedRing α] {a b c : α}

-- theorem OrderedRing.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b := by
--   rw [← sub_pos, ← mul_sub]
--   exact OrderedRing.mul_pos _ _ h₂ (sub_pos.2 h₁)

-- theorem OrderedRing.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c := by
--   rw [← sub_pos, ← sub_mul]
--   exact OrderedRing.mul_pos _ _ (sub_pos.2 h₁) h₂

-- -- see Note [lower instance priority]
-- instance (priority := 100) OrderedRing.toOrderedSemiring : OrderedSemiring α :=
--   { ‹OrderedRing α›, Ring.toSemiring with
--     le_of_add_le_add_left := @le_of_add_le_add_left α _ _ _,
--     mul_lt_mul_of_pos_left := @OrderedRing.mul_lt_mul_of_pos_left α _,
--     mul_lt_mul_of_pos_right := @OrderedRing.mul_lt_mul_of_pos_right α _ }

-- theorem mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
--   have : -c > 0 := neg_pos_of_neg hc
--   have : b * -c < a * -c := mul_lt_mul_of_pos_right h this
--   have : -(b * c) < -(a * c) := by rwa [mul_neg, mul_neg] at this
--   lt_of_neg_lt_neg this

-- theorem mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b := by
--   have : 0 * b < a * b := mul_lt_mul_of_neg_right ha hb
--   rwa [zero_mul] at this

-- end OrderedRing
