/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Tactic.Linter.OldObtain

/-! Tests for the `oldObtain` linter. -/

-- These cases are fine.
theorem foo : True := by
  obtain := trivial
  obtain _h := trivial
  obtain : True := trivial
  obtain _h : True := trivial
  trivial

-- These cases are linted against.

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem foo' : True := by
  obtain : True
  · trivial
  trivial

set_option linter.oldObtain false in
/--
warning: Please remove stream-of-conciousness `obtain` syntax
note: this linter can be disabled with `set_option linter.oldObtain false`
-/
#guard_msgs in
set_option linter.oldObtain true in
theorem foo'' : True := by
  obtain h : True
  · trivial
  trivial
