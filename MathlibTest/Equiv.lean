import Mathlib.Data.Int.Order.Units
import Mathlib.GroupTheory.Perm.Finite

example : orderOf (-1 : ℤˣ) = 2 :=
  orderOf_eq_prime (Int.units_sq _) (by decide)
