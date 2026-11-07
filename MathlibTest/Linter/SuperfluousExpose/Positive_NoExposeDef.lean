/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: defs whose bodies Lean hides in every public section, even with the section
modifier: an `@[no_expose] def` and a `meta def` outside a `meta` section. The linter must
fire. -/

@[expose] public section

namespace SuperfluousExposeTest.NoExposeDef

@[no_expose] def hiddenValue : Nat := 1

meta def metaValue : Nat := 2

theorem hiddenValue_eq : hiddenValue = hiddenValue := rfl

end SuperfluousExposeTest.NoExposeDef

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
