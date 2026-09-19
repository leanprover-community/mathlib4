/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: only theorems. Lean hides a proof in every public section. The linter must
fire. -/

@[expose] public section

namespace SuperfluousExposeTest.TheoremOnly

theorem one_eq_one : 1 = 1 := rfl
theorem two_plus_two : 2 + 2 = 4 := by decide
theorem three_pos : 0 < 3 := by decide

end SuperfluousExposeTest.TheoremOnly

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
