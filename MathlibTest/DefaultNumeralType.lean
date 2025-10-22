/-
Copyright (c) 2025 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
import Mathlib.Tactic.DefaultNumeralType
import Mathlib.Data.Rat.Defs

/-!
# Tests for `set_default_numeral_type`

This file tests the `set_default_numeral_type` command which provides a user-friendly
way to set the default type for numeric literals without needing to know the instance name.
-/

-- Test with Rat (Rational numbers)
set_default_numeral_type Rat

/-- info: 1 : Rat -/
#guard_msgs in
#check 1

/-- info: 42 : Rat -/
#guard_msgs in
#check 42

-- Reset to default (Nat)
set_default_numeral_type Nat

/-- info: 1 : Nat -/
#guard_msgs in
#check 1
