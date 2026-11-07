/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a `@[reducible] def`. Lean exposes the body of an `abbrev` in every public
section, but the section modifier controls the body of a `@[reducible] def`, and the public `rfl`
proof below reads it. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ReducibleDef

@[reducible] def double (n : Nat) : Nat := n + n

@[simp] theorem double_zero : double 0 = 0 := rfl

end SuperfluousExposeTest.ReducibleDef
