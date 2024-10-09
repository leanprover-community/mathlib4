/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser
-/
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Semireal rings

A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring.

For instance, linearly ordered fields are semireal, because sums of squares are positive and `-1` is
not. More generally, linearly ordered semirings in which `a ≤ b → ∃ c, a + c = b` holds, are
semireal.

## Main declaration

- `IsSemireal`: the predicate asserting that a commutative ring `R` is semireal.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
[lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

variable (R : Type*)

/--
A semireal ring is a non-trivial commutative ring (with unit) in which `-1` is *not* a sum of
squares. Note that `-1` does not make sense in a semiring. Below we define the class `IsSemireal R`
for all additive monoid `R` equipped with a multiplication, a multiplicative unit and a negation.
-/
@[mk_iff]
class IsSemireal [AddMonoid R] [Mul R] [One R] [Neg R] : Prop where
  non_trivial         : (0 : R) ≠ 1
  not_isSumSq_neg_one : ¬IsSumSq (-1 : R)

@[deprecated (since := "2024-08-09")] alias isSemireal := IsSemireal
@[deprecated (since := "2024-08-09")] alias isSemireal.neg_one_not_SumSq :=
  IsSemireal.not_isSumSq_neg_one

instance [LinearOrderedRing R] : IsSemireal R where
  non_trivial := zero_ne_one
  not_isSumSq_neg_one := fun h ↦ (not_le (α := R)).2 neg_one_lt_zero h.nonneg
