/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Nonneg.Field
public import Mathlib.Algebra.Order.Ring.Rat

import Mathlib.Data.Rat.Cast.CharZero

/-!
# The rational numbers form a linear ordered field

This file used to contain the linear ordered field instance on the rational numbers.

TODO: rename this file to `Mathlib/Algebra/Order/GroupWithZero/NNRat.lean`

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

public section

namespace NNRat
variable {K : Type*} [DivisionRing K] [CharZero K]

deriving instance LinearOrderedCommGroupWithZero for NNRat

@[simp] lemma cast_sub {p q : ℚ≥0} (h : p ≤ q) : (↑(q - p) : K) = q - p := by
  rw [eq_sub_iff_add_eq]; norm_cast; exact tsub_add_cancel_of_le h

end NNRat
