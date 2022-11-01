/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/

import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Int.Notation

/-! # The order relation on the integers -/

open Nat

namespace Int

instance : LinearOrder ℤ where
  le := (·≤·)
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  lt := (·<·)
  lt_iff_le_not_le := @Int.lt_iff_le_not_le
  le_total := Int.le_total
  decidable_eq := by infer_instance
  decidable_le := by infer_instance
  decidable_lt := by infer_instance
