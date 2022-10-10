import Mathlib.Algebra.Group.Defs

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

/-! ### Additive monoids with one -/

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where
  natCast : ℕ → R
  natCast_zero : natCast 0 = 0
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1

@[coe]
def Nat.cast [AddMonoidWithOne R] : ℕ → R := AddMonoidWithOne.natCast

instance [AddMonoidWithOne R] : CoeTail ℕ R where coe := Nat.cast
instance [AddMonoidWithOne R] : CoeHTCT ℕ R where coe := Nat.cast

@[simp, norm_cast] theorem Nat.cast_zero [AddMonoidWithOne R] : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
@[simp 500, norm_cast 500]
theorem Nat.cast_succ [AddMonoidWithOne R] : ((Nat.succ n : ℕ) : R) = (n : R) + 1 :=
  AddMonoidWithOne.natCast_succ _
@[simp, norm_cast]
theorem Nat.cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by simp

@[simp, norm_cast] theorem Nat.cast_add [AddMonoidWithOne R] : ((m + n : ℕ) : R) = (m : R) + n := by
  induction n <;> simp_all [add_succ, add_assoc]

class Nat.AtLeastTwo (n : Nat) : Prop where
  prop : n ≥ 2
instance : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _

@[nolint unusedArguments]
instance [AddMonoidWithOne R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast

@[simp, norm_cast] theorem Nat.cast_ofNat [AddMonoidWithOne R] [Nat.AtLeastTwo n] :
  (Nat.cast (OfNat.ofNat n) : R) = OfNat.ofNat n := rfl

/-! ### Additive groups with one -/

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where
  intCast : ℤ → R
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - natCast (n + 1)

@[coe]
def Int.cast [AddGroupWithOne R] : ℤ → R := AddGroupWithOne.intCast

instance [AddGroupWithOne R] : CoeTail ℤ R where coe := Int.cast

theorem Int.cast_ofNat [AddGroupWithOne R] : (Int.cast (Int.ofNat n) : R) = Nat.cast n :=
  AddGroupWithOne.intCast_ofNat _
@[simp, norm_cast]
theorem Int.cast_negSucc [AddGroupWithOne R] :
    (Int.cast (Int.negSucc n) : R) = (-(Nat.cast (n + 1)) : R) :=
  AddGroupWithOne.intCast_negSucc _

@[simp, norm_cast] theorem Int.cast_zero [AddGroupWithOne R] : ((0 : ℤ) : R) = 0 := by
  erw [Int.cast_ofNat, Nat.cast_zero]
@[simp, norm_cast] theorem Int.cast_one [AddGroupWithOne R] : ((1 : ℤ) : R) = 1 := by
  erw [Int.cast_ofNat, Nat.cast_one]
