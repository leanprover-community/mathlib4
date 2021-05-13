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

/-

Probably need a theory of AddRightCancelMonoids and AddLeftCancelMonoids
for this:

-/

-- theorem Ring.zero_mul {R : Type u} [Ring R] (a : R) : 0 * a = 0 := by
  
/- 

Need to think harder about this `h with` issue in the below:

-/

-- instance (R : Type u) [h : Ring R] : Semiring R :=
-- { h with 
--   zero_mul := sorry
--   mul_zero := sorry
-- }

/- 

TODO

-/

-- declare instance from ring to semiring
-- comm_ring : extends ring
-- declare instance from comm_ring to comm_semiring
