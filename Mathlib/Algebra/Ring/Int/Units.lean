/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Algebra.Ring.Units

/-!
# Basic lemmas for `ℤˣ`.

This file contains lemmas on the units of `ℤ`.

## Main results

* `Int.units_eq_one_or`: the invertible integers are 1 and -1.

See note [foundational algebra order theory].
-/

public section

assert_not_exists DenselyOrdered Set.Subsingleton

namespace Int

/-! #### Units -/

lemma units_eq_one_or (u : ℤˣ) : u = 1 ∨ u = -1 := by
  simpa only [Units.ext_iff] using! isUnit_eq_one_or u.isUnit

lemma units_ne_iff_eq_neg {u v : ℤˣ} : u ≠ v ↔ u = -v := by
  simpa only [Ne, Units.ext_iff] using! isUnit_ne_iff_eq_neg u.isUnit v.isUnit

end Int

namespace MonoidWithZeroHom

variable {M : Type*} [MonoidWithZero M] (f : M →*₀ ℤ) {b : M}

/-- The image of a unit under an arbitrary homomorphism to the integers is 1 or -1. -/
lemma eq_one_or_neg_one (hb : IsUnit b) : f b = 1 ∨ f b = -1 := Int.isUnit_eq_one_or (hb.map f)

/-- The square of the image of 'b' under a homomorphism to the integers is 1 if 'b' is a unit. -/
theorem sq_one (hb : IsUnit b) : f b ^ 2 = 1 := by
  cases eq_one_or_neg_one f hb <;> aesop

end MonoidWithZeroHom
