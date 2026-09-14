/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: only `abbrev` declarations. Lean exposes the body of an
`abbrev` in every public section, so the modifier adds nothing. The linter
must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.AbbrevOnly

abbrev MyNat := Nat
abbrev double (n : Nat) : Nat := n + n

theorem double_zero : double 0 = 0 := rfl

end SuperfluousExposeTest.AbbrevOnly

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
