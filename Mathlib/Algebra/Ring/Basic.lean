import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Group.Basic
/-

# Semirings and rings

-/

class Semiring (R : Type u) extends Monoid R, AddCommMonoid R where
  zero_mul (a : R) : 0 * a = 0
  mul_zero (a : R) : a * 0 = 0
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c

instance (R : Type u) [h : Semiring R] : MonoidWithZero R :=
{ h with }

class CommSemiring (R : Type u) extends Semiring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [h : CommSemiring R] : CommMonoid R :=
{ h with }

class Ring (R : Type u) extends Monoid R, AddCommGroup R where
  mul_add (a b c : R) : a * (b + c) = a * b + a * c
  add_mul (a b c : R) : (a + b) * c = a * c + b * c

-- I need to name this instance and I don't know the default name
instance Ring.toSemiring (R : Type u) [h : Ring R] : Semiring R :=
{ h with
  toAddCommMonoid := AddCommGroup.toAddCommMonoid R
  zero_mul := λ a => by rw [← add_right_eq_self (a := 0 * a), ← Ring.add_mul, zero_add]
  mul_zero := λ a => by rw [← add_right_eq_self (a := a * 0), ← Ring.mul_add, add_zero]
}

class CommRing (R : Type u) extends Ring R where
  mul_comm (a b : R) : a * b = b * a

instance (R : Type u) [h : CommRing R] : CommSemiring R :=
{ h with
  toSemiring := Ring.toSemiring R 
}

