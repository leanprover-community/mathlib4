/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a `@[reducible] def`. Only an `abbrev` carries its own
exposure, so the `@[expose]` of the section controls this body: the `rfl`
proof below needs it, in the public scope of this same file. The linter must
not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ReducibleDef

@[reducible] def double (n : Nat) : Nat := n + n

@[simp] theorem double_zero : double 0 = 0 := rfl

end SuperfluousExposeTest.ReducibleDef
