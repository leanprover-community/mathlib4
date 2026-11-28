/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: only theorems, in a section that the end of the file closes. `#exit` is a
terminal command, so the linter settles the open section there. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.FileEndClose

theorem one_eq_one : 1 = 1 := rfl

end SuperfluousExposeTest.FileEndClose

/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
