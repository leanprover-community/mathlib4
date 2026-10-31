/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: only a structure. Lean exposes the bodies of its projections in every public
section, its recursors have no body, and its other generated constants are auto-declarations.
The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Structure

structure Point where
  x : Nat
  y : Nat

theorem point_zero_zero : (⟨0, 0⟩ : Point).x = 0 := rfl

end SuperfluousExposeTest.Structure

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
