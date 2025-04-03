/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.NNRat.Defs

/-!
# The rational numbers form a linear ordered field

This file contains the linear ordered field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

instance : IsOrderedMonoidWithZero NNRat :=
  Nonneg.isOrderedMonoidWithZero
