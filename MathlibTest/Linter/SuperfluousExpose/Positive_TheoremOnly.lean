/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: file with only theorems → linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.TheoremOnly

theorem one_eq_one : 1 = 1 := rfl
theorem two_plus_two : 2 + 2 = 4 := by decide
theorem three_pos : 0 < 3 := by decide

end SuperfluousExposeTest.TheoremOnly
-- Expected: linter warning at end-of-file.
