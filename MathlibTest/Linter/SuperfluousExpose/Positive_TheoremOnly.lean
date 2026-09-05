/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: the file contains only theorems. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.TheoremOnly

theorem one_eq_one : 1 = 1 := rfl
theorem two_plus_two : 2 + 2 = 4 := by decide
theorem three_pos : 0 < 3 := by decide

end SuperfluousExposeTest.TheoremOnly

-- `#exit` is a terminal command, so the linter fires there and `#guard_msgs`
-- can capture the warning. The linter option is off at the real end of the
-- file, so the linter is silent there.
set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from body exposure. You can safely remove the `@[expose]` modifier: it only affects `def` and `inductive` bodies, and no declaration here needs exposure (only theorems, instances, classes, structures, abbrevs, notation, or auto-generated declarations).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
