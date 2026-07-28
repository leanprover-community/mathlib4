/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: the file contains only a structure. A structure produces
auto-generated `.rec`, `.recOn`, and `.casesOn` constants and projection
defs. None of these benefit from exposure. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Recursors

structure Point where
  x : Nat
  y : Nat

theorem point_zero_zero : (⟨0, 0⟩ : Point).x = 0 := rfl

end SuperfluousExposeTest.Recursors

-- `#exit` is a terminal command, so the linter fires there and `#guard_msgs`
-- can capture the warning. The linter option is off at the real end of the
-- file, so the linter is silent there.
set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This module has `@[expose] public section` but no declaration that would benefit from body exposure. The `@[expose]` modifier can be safely removed: it would only affect `def`/`inductive` bodies, and there are none here that need exposure (only theorems, instances, classes/structures, abbrevs, notation, or auto-generated decls).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
