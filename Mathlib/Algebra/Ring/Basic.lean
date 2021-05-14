import Mathlib.Algebra.GroupWithZero.Defs
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

-- TODO: prove zero_mul and mul_zero

-- instance (R : Type u) [h : Ring R] : Semiring R :=
-- { h with
--   toAddCommMonoid := AddCommGroup.toAddCommMonoid R
--   zero_mul := sorry
--   mul_zero := sorry
-- }
-- Proof: 0*r=(0+0)*r=0*r+0*r etc

-- TODO
-- comm_ring : extends ring
-- declare instance from comm_ring to comm_semiring
