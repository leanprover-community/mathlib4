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

variable {R : Type*}

variable (R) in
/--
A semireal ring is a commutative ring (with unit) in which `-1` is *not* a sum of
squares. We define the predicate `IsSemireal R` for structures `R` equipped with
a multiplication, an addition, a multiplicative unit and an additive unit.
-/
@[mk_iff]
class IsSemireal [Add R] [Mul R] [One R] [Zero R] : Prop where
  one_add_ne_zero {s : R} (hs : IsSumSq s) : 1 + s ≠ 0

/-- In a semireal ring, `-1` is not a sum of squares. -/
theorem IsSemireal.not_isSumSq_neg_one [AddGroup R] [One R] [Mul R] [IsSemireal R] :
    ¬ IsSumSq (-1 : R) := (by simpa using one_add_ne_zero ·)

/--
Linearly ordered semirings with the property `a ≤ b → ∃ c, a + c = b` (e.g. `ℕ`)
are semireal.
-/
instance [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R] : IsSemireal R where
  one_add_ne_zero hs amo := zero_ne_one' R (le_antisymm zero_le_one
                              (le_of_le_of_eq (le_add_of_nonneg_right hs.nonneg) amo))
