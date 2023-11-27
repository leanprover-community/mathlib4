/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.ContinuedFractions.Basic

#align_import algebra.continued_fractions.computation.basic from "leanprover-community/mathlib"@"a7e36e48519ab281320c4d192da6a7b348ce40ad"

/-!
# Computable Continued Fractions

## Summary

We formalise the standard computation of (regular) continued fractions for linear ordered floor
fields. The algorithm is rather simple. Here is an outline of the procedure adapted from Wikipedia:

Take a value `v`. We call `⌊v⌋` the *integer part* of `v` and `v - ⌊v⌋` the *fractional part* of
`v`.  A continued fraction representation of `v` can then be given by `CF[⌊v⌋; b₀, b₁, b₂,...]`,
where `CF[b₀; b₁, b₂,...]` recursively is the continued fraction representation of `1 / (v - ⌊v⌋)`.  This
process stops when the fractional part hits 0.

In other words: to calculate a continued fraction representation of a number `v`, write down the
integer part (i.e. the floor) of `v`. Subtract this integer part from `v`. If the difference is 0,
stop; otherwise find the reciprocal of the difference and repeat. The procedure will terminate if
and only if `v` is rational.

For an example, refer to `CF.of`.

## Main definitions

- `CF.of`: computes the generalised continued fraction of a value `v`.
  In fact, it computes a regular continued fraction that terminates if and only if `v` is rational.

## Implementation Notes

The computation is implemented using corecursion.

## References

- https://en.wikipedia.org/wiki/Continued_fraction

## Tags

numerics, number theory, approximations, fractions
-/

universe u

open Int Stream'.Seq

namespace CF

-- Note: this could be relaxed to something like `LinearOrderedDivisionRing` in the future.
-- Fix a discrete linear ordered field with `floor` function.
variable {K : Type u} [LinearOrderedField K] [FloorRing K]

#noalign generalized_continued_fraction.int_fract_pair

#noalign generalized_continued_fraction.int_fract_pair.has_repr

#noalign generalized_continued_fraction.int_fract_pair.inhabited

set_option linter.uppercaseLean3 false in
#noalign generalized_continued_fraction.int_fract_pair.mapFr

#noalign generalized_continued_fraction.int_fract_pair.has_coe_to_int_fract_pair

#noalign generalized_continued_fraction.int_fract_pair.coe_to_int_fract_pair

#noalign generalized_continued_fraction.int_fract_pair.of

#noalign generalized_continued_fraction.int_fract_pair.stream_is_seq

#noalign generalized_continued_fraction.int_fract_pair.seq1

/-- Returns the `CF` of a value. In fact, the returned cf terminates if and only if `v` is rational.

The continued fraction representation of `v` is given by `CF[⌊v⌋; b₀, b₁, b₂,...]`, where
`b₀, b₁, b₂,...` is corecursively defined by `CF.of.next?` from `fract v`.

For example, let `(v : ℚ) := 3.4`. The process goes as follows:
```lean
(CF.of v).h             :=   3     ←⌊·⌋-    3.4
                                            ↓ fract
                                           0.4
                                            ↓ of.next?
(CF.of v).sb.get? 0     := some 2   ←   some (2, 0.5)
                                            ↓
                                           0.5
                                            ↓ of.next?
(CF.of v).sb.get? 1     := some 2   ←   some (2, 0)
                                            ↓
                                            0
                                            ↓ of.next?
(CF.of v).sb.get? n ≥ 2 :=  none    ←     none
```
-/
@[simps]
protected def of (v : K) : CF K where
  h  := ⌊v⌋
  sb := corec next? ⟨fract v, ⟨fract_nonneg v, fract_lt_one v⟩⟩
where
  /-- Creates the pair of integer and fractional parts of a value `v⁻¹` for `0 < v < 1`.
  If `v = 0`, returns `none`.
  -/
  next? : { v : K // 0 ≤ v ∧ v < 1 } → Option (ℕ+ × { v : K // 0 ≤ v ∧ v < 1 })
    | ⟨v, hv⟩ =>
      if hvn : v = 0 then
        none
      else
        have hvo : 0 < ⌊v⁻¹⌋₊ := by
          rcases hv with ⟨hvge, hvlt⟩
          rw [Nat.floor_pos, one_le_inv_iff, lt_iff_le_and_ne, ne_comm]
          exact ⟨⟨hvge, hvn⟩, le_of_lt hvlt⟩
        some (Nat.toPNat ⌊v⁻¹⌋₊ hvo, ⟨fract v⁻¹, ⟨fract_nonneg v⁻¹, fract_lt_one v⁻¹⟩⟩)
#align generalized_continued_fraction.of CF.ofₓ
#align generalized_continued_fraction.int_fract_pair.stream CF.of.next?ₓ

end CF
