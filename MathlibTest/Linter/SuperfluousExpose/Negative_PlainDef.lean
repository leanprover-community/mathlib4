/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: file contains a real plain `def`. Its body matters
downstream (rfl/simp/unfold). Linter must NOT fire. -/

@[expose] public section

namespace SuperfluousExposeTest.PlainDef

def addOne (n : Nat) : Nat := n + 1

theorem addOne_zero : addOne 0 = 1 := rfl

end SuperfluousExposeTest.PlainDef
-- Expected: NO linter warning.
