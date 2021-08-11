import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Spread
/-

# Semirings and rings

-/

class Numeric (α : Type u) where
  ofNat : Nat → α

instance Numeric.OfNat [Numeric α] : OfNat α n := ⟨Numeric.ofNat n⟩
instance [Numeric α] : Coe ℕ α := ⟨Numeric.ofNat⟩

class Semiring (R : Type u) extends Monoid R, AddCommMonoid R, Numeric R where
  zero_mul (a : R) : 0 * a = 0
  mul_zero (a : R) : a * 0 = 0
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b
  ofNat_one : ofNat (nat_lit 1) = One.one
  ofNat_zero : ofNat (nat_lit 0) = Zero.zero

section Semiring
variable {R} [Semiring R]
instance : MonoidWithZero R where
  __ := ‹Semiring R›

theorem mul_add  (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

theorem add_mul {R} [Semiring R] (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] theorem mul_zero {R} [Semiring R] (a : R) : a * 0 = 0 := Semiring.mul_zero a

@[simp] theorem zero_mul {R} [Semiring R] (a : R) : 0 * a = 0 := Semiring.zero_mul a

theorem Semiring.ofNat_pow (a n : ℕ) : Numeric.ofNat (a^n) = (Numeric.ofNat a : R)^n := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.pow_zero, Semiring.ofNat_one]
    exact rfl
  | succ n ih =>
    rw [pow_succ, Nat.pow_succ, Semiring.ofNat_mul, ih]

end Semiring

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommSemiring R] : CommMonoid R where
  __ := ‹CommSemiring R›

class Ring (R : Type u) extends Monoid R, AddCommGroup R, Numeric R where
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b
  ofNat_one : ofNat (nat_lit 1) = One.one
  ofNat_zero : ofNat (nat_lit 0) = Zero.zero

instance (R : Type u) [Ring R] : Semiring R where
  zero_mul := λ a => by rw [← add_right_eq_self (a := 0 * a), ← Ring.add_mul, zero_add]
  mul_zero := λ a => by rw [← add_right_eq_self (a := a * 0), ← Ring.mul_add, add_zero]
  __ := ‹Ring R›

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [CommRing R] : CommSemiring R where
  __ := inferInstanceAs (Semiring R)
  __ := ‹CommRing R›

/- Instances -/

namespace Nat

instance : Numeric Nat := ⟨id⟩
@[simp] theorem ofNat_eq_Nat (n : Nat): Numeric.ofNat n = n := rfl

instance : CommSemiring Nat where
  mul_comm := Nat.mul_comm
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  ofNat_add := by simp
  ofNat_mul := by simp
  ofNat_one := rfl
  ofNat_zero := rfl
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow (n x) := HPow.hPow x n
  npow_zero' := Nat.pow_zero
  npow_succ' n x := by simp [Nat.pow_succ, Nat.mul_comm]
  one := 1
  zero := 0
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := HMul.hMul
  nsmul_zero' := Nat.zero_mul
  nsmul_succ' n x := by simp [Nat.add_comm, (Nat.succ_mul n x)]
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

end Nat
