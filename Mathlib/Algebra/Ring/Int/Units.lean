/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Units

/-!
# Basic lemmas for `ℤˣ`.

This file contains lemmas on the units of `ℤ`.

## Main results

 * `Int.units_eq_one_or`: the invertible integers are 1 and -1.

See note [foundational algebra order theory].
-/

assert_not_exists DenselyOrdered
assert_not_exists Set.Subsingleton

namespace Int

/-! #### Units -/

lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using isUnit_eq_one_or u.isUnit

lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using isUnit_ne_iff_eq_neg u.isUnit v.isUnit

end Int
