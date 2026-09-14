/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Three expose sections in one file, to show that each section gets its
own verdict. Sections one and three hold only theorems and must each get a
warning. Section two holds a def and must stay silent. -/

set_option linter.superfluousExpose true

@[expose] public section

theorem first_section : 1 = 1 := rfl

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end

@[expose] public section

def keeper : Nat := 5

#guard_msgs in
end

@[expose] public section

theorem third_section : 2 = 2 := rfl

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
