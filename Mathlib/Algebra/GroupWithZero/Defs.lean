import Mathlib.Algebra.Group.Defs

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, Zero M₀ where
  zero_mul (a : M₀) : 0 * a = 0
  mul_zero (a : M₀) : a * 0 = 0

class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, Inv G₀, Div G₀ where
  mul_left_inv (a : G₀) : a⁻¹ * a = 1
  div_eq_mul_inv (a b : G₀) : a / b = a * b⁻¹ 
  gpow : ℤ → G₀ → G₀ := gpow_rec
  gpow_zero' (a : G₀) : gpow 0 a = 1 -- try rfl
  gpow_succ' (n : ℕ) (a : G₀) : gpow (Int.ofNat n.succ) a = a * gpow (Int.ofNat n) a 
  gpow_neg' (n : ℕ) (a : G₀) : gpow (Int.negSucc n) a = (gpow ↑(n.succ) a)⁻¹
  exists_pair_ne : ∃ (x y : G₀), x ≠ y
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1