import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.NeZero

theorem eq_of_sub_eq_zero' [AddGroup R] {a b : R} (h : a - b = 0) : a = b :=
  add_right_cancel <| show a + (-b) = b + (-b) by rw [← sub_eq_add_neg, h, add_neg_self]

theorem pow_succ'' [Monoid M] : ∀ (n : ℕ) (a : M), a ^ n.succ = a * a ^ n :=
Monoid.npow_succ'

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

export MonoidWithZero (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

class GroupWithZero (G₀ : Type u) extends DivInvMonoid G₀, MonoidWithZero G₀ where
  exists_pair_ne : ∃ (x y : G₀), x ≠ y
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

export GroupWithZero (inv_zero)
attribute [simp] inv_zero

section NeZero

attribute [field_simps] two_ne_zero three_ne_zero four_ne_zero

end NeZero
