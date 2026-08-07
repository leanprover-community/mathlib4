/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains a `@[reducible] def`. Unlike an
`abbrev`, it does not carry its own exposure, so the section's `@[expose]`
is load-bearing: without it, the `rfl` proof below fails in the public
scope of this very file. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ReducibleDef

@[reducible] def double (n : Nat) : Nat := n + n

@[simp] theorem double_zero : double 0 = 0 := rfl

end SuperfluousExposeTest.ReducibleDef
-- Expected: no linter warning.
