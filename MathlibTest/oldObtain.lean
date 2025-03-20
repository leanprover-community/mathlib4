/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Tactic.Linter.OldObtain

/-! Tests for the `oldObtain` linter. -/

set_option linter.oldObtain true

-- These cases are fine.
theorem foo : True := by
  obtain := trivial
  obtain _h := trivial
  obtain : True := trivial
  obtain _h : True := trivial
  trivial

-- These cases are linted against.

/--
warning: Please remove stream-of-consciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
theorem foo' : True := by
  obtain : True
  · trivial
  trivial

/--
warning: Please remove stream-of-consciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
theorem foo'' : True := by
  obtain h : True
  · trivial
  trivial
