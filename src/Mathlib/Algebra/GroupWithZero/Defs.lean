import Mathlib.Algebra.Group.Defs

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, Zero M₀ where
  zero_mul (a : M₀) : 0 * a = 0
  mul_zero (a : M₀) : a * 0 = 0

export MonoidWithZero (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

class GroupWithZero (G₀ : Type u) extends DivInvMonoid G₀, MonoidWithZero G₀ where
  exists_pair_ne : ∃ (x y : G₀), x ≠ y
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

export GroupWithZero (inv_zero)
attribute [simp] inv_zero
