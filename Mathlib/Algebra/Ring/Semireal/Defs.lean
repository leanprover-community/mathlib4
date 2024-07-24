/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/

import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.Algebra.Order.Field.Defs

/-!
# Semireal rings

A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring.

For instance, linearly ordered fields are semireal, because sums of squares are positive and `-1` is
not. More generally, linearly ordered semirings in which `a ≤ b → ∃ c, a + c = b` holds, are
semireal.

## Main declaration

- `isSemireal`: the predicate asserting that a commutative ring `R` is semireal.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
[lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

variable (R : Type*)

/--
A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring. Below we define the class `isSemiReal R`
for all additive monoid `R` equipped with a multiplication, a multiplicative unit and a negation.
-/
@[mk_iff]
class isSemireal [AddMonoid R] [Mul R] [One R] [Neg R] : Prop where
  non_trivial        : (0 : R) ≠ 1
  neg_one_not_SumSq  : ¬isSumSq (-1 : R)

instance [LinearOrderedField R] : isSemireal R where
  non_trivial := zero_ne_one
  neg_one_not_SumSq := fun h ↦ (not_le (α := R)).2 neg_one_lt_zero h.nonneg
