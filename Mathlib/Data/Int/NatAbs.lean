/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Jeremy Tan
-/
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Ring.Int.Defs

/-!
# Lemmas about `Int.natAbs`

This file contains some results on `Int.natAbs`, the absolute value of an integer as a
natural number.

## Main results

* `Int.natAbsHom`: `Int.natAbs` bundled as a `MonoidWithZeroHom`.
-/

namespace Int

/-- `Int.natAbs` as a bundled `MonoidWithZeroHom`. -/
@[simps]
def natAbsHom : ℤ →*₀ ℕ where
  toFun := Int.natAbs
  map_mul' := Int.natAbs_mul
  map_one' := Int.natAbs_one
  map_zero' := Int.natAbs_zero

lemma natAbs_natCast_sub_natCast_of_ge {a b : ℕ} (h : b ≤ a) : Int.natAbs (↑a - ↑b) = a - b := by
  cutsat

lemma natAbs_natCast_sub_natCast_of_le {a b : ℕ} (h : a ≤ b) : Int.natAbs (↑a - ↑b) = b - a := by
  cutsat

end Int
