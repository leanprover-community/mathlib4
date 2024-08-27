/-
Copyright (c) 2024 Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florent Schaffhauser, Artie Khovanov
-/
import Mathlib.Algebra.Ring.SumsOfSquares

/-!
# Semireal rings

A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum of squares.

For instance, linearly ordered rings are semireal, because sums of squares are positive and `-1` is
not.

## Main declaration

- `IsSemireal`: the predicate asserting that a commutative ring `R` is semireal.

## References

- *An introduction to real algebra*, by T.Y. Lam. Rocky Mountain J. Math. 14(4): 767-814 (1984).
[lam_1984](https://doi.org/10.1216/RMJ-1984-14-4-767)
-/

variable (R : Type*)

/--
A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum of
squares. We define the class `IsSemireal R` for all structures equipped with
a multiplication, an addition, a multiplicative unit and an additive unit.
-/
@[mk_iff]
class IsSemireal [Add R] [Mul R] [One R] [Zero R] : Prop where
  add_one_ne_zero_of_isSumSq (a : R) (ssa : IsSumSq a) : 1 + a ≠ 0

@[deprecated (since := "2024-08-09")] alias isSemireal := IsSemireal
@[deprecated (since := "2024-08-09")] alias isSemireal.neg_one_not_SumSq :=
  IsSemireal.add_one_ne_zero_of_isSumSq

/-- Linearly ordered semirings in which the property `a ≤ b → ∃ c, a + c = b` holds are semireal. -/
instance [LinearOrderedSemiring R] [ExistsAddOfLE R] : IsSemireal R where
  add_one_ne_zero_of_isSumSq _ ssa amo :=
    zero_ne_one' R (le_antisymm zero_le_one
      (le_of_le_of_eq (le_add_of_nonneg_right ssa.nonneg) amo))
