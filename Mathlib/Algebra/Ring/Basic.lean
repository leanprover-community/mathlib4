import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
/-

# Semirings and rings

-/

class Numeric (α : Type u) where
  ofNat : Nat → α

instance Numeric.OfNat [Numeric α] : OfNat α n := ⟨Numeric.ofNat n⟩

class Semiring (R : Type u) extends Monoid R, AddCommMonoid R, Numeric R where
  zero_mul (a : R) : 0 * a = 0
  mul_zero (a : R) : a * 0 = 0
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b

instance (R : Type u) [h : Semiring R] : MonoidWithZero R :=
{ h with }

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [h : CommSemiring R] : CommMonoid R :=
{ h with }

class Ring (R : Type u) extends Monoid R, AddCommGroup R, Numeric R where
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b

instance (R : Type u) [h : Ring R] : Semiring R :=
{ h with
  toAddCommMonoid := inferInstance
  zero_mul := λ a => by rw [← add_right_eq_self (a := 0 * a), ← Ring.add_mul, zero_add]
  mul_zero := λ a => by rw [← add_right_eq_self (a := a * 0), ← Ring.mul_add, add_zero]
}

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [h : CommRing R] : CommSemiring R :=
{ h with toSemiring := inferInstance }

