/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Bound

/-!
## Tests for the `@bound` attribute

Verify that our heuristic for the priority of a declaration produces the expected values.
-/

open Mathlib.Tactic.Bound (declPriority)

/-- info: 0 -/
#guard_msgs in
#eval declPriority `le_refl

/-- info: 0 -/
#guard_msgs in
#eval declPriority `sq_nonneg

/-- info: 11 -/
#guard_msgs in
#eval declPriority `Bound.one_lt_div_of_pos_of_lt

/-- info: 141 -/
#guard_msgs in
#eval declPriority `Bound.pow_le_pow_right_of_le_one_or_one_le
