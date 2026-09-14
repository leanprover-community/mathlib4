/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: only a structure. It produces `.rec`, `.recOn` and
`.casesOn` constants and projection defs, and all of them follow the
visibility of the structure. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Recursors

structure Point where
  x : Nat
  y : Nat

theorem point_zero_zero : (⟨0, 0⟩ : Point).x = 0 := rfl

end SuperfluousExposeTest.Recursors

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
