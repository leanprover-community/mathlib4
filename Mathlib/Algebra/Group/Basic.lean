import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Basic

section AddCommSemigroup_lemmas

variable {A : Type u} [AddCommSemigroup A]

theorem add_add_add_comm (a b c d : A) : (a + b) +(c + d) = (a + c) + (b + d) :=
by simp [add_left_comm, add_assoc]

end AddCommSemigroup_lemmas

section CommSemigroup_lemmas

variable {M : Type u} [CommSemigroup M]

theorem mul_mul_mul_comm (a b c d : M) : (a * b) * (c * d) = (a * c) * (b * d) :=
by simp [mul_assoc, mul_left_comm]

end CommSemigroup_lemmas

-- section DivisionMonoid

-- variable [DivisionMonoid α] {a b c : α}

-- attribute [local simp] mul_assoc div_eq_mul_inv

-- @[to_additive]
-- theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by rw [← inv_eq_of_mul_eq_one_right h, inv_invₓ]

-- @[to_additive]
-- theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
--   (inv_eq_of_mul_eq_one_left h).symm

-- @[to_additive]
-- theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
--   (inv_eq_of_mul_eq_one_right h).symm

-- @[to_additive]
-- theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_left h, one_div]

-- @[to_additive]
-- theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by rw [eq_inv_of_mul_eq_one_right h, one_div]

-- @[to_additive]
-- theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
--   inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]

-- @[to_additive]
-- theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
--   mt eq_of_div_eq_one

-- variable (a b c)

-- @[to_additive]
-- theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp

-- @[to_additive]
-- theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp

-- @[simp, to_additive]
-- theorem inv_div : (a / b)⁻¹ = b / a := by simp

-- @[simp, to_additive]
-- theorem one_div_div : 1 / (a / b) = b / a := by simp

-- @[to_additive]
-- theorem one_div_one_div : 1 / (1 / a) = a := by simp

-- @[to_additive]
-- instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
--   { DivisionMonoid.toDivInvMonoid α with inv_one := by simpa only [one_div, inv_invₓ] using (inv_div (1 : α) 1).symm }

-- variable {a b c}

-- @[simp, to_additive]
-- theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
--   inv_injective.eq_iff' inv_one

-- @[simp, to_additive]
-- theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
--   eq_comm.trans inv_eq_one

-- @[to_additive]
-- theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
--   inv_eq_one.Not

-- @[to_additive]
-- theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by rw [← one_div_one_div a, h, one_div_one_div]

-- variable (a b c)

-- -- The attributes are out of order on purpose
-- @[to_additive, field_simps]
-- theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp

-- @[simp, to_additive]
-- theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp

-- @[to_additive]
-- theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]

-- end DivisionMonoid
