import Mathlib.Algebra.Group.Defs

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, Zero M₀ where
  zero_mul (a : M₀) : 0 * a = 0
  mul_zero (a : M₀) : a * 0 = 0

class GroupWithZero (G₀ : Type u) extends DivInvMonoid G₀, Zero G₀ where
  exists_pair_ne : ∃ (x y : G₀), x ≠ y
  zero_mul (a : G₀) : 0 * a = 0
  mul_zero (a : G₀) : a * 0 = 0
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

instance (G₀ : Type u) [h : GroupWithZero G₀] : MonoidWithZero G₀ :=
{h with }
