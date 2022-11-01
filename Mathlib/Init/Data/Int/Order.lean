/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Init.Data.Int.Basic

/-!
# The order relation on the integers.
-/

namespace Int

instance : LinearOrder Int where
  le := Int.le
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := Int.lt
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidable_eq := inferInstance
  decidable_le := inferInstance
  decidable_lt := inferInstance
