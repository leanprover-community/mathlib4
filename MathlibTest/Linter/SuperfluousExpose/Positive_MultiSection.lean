/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! One file with three expose sections. Sections one and three contain only
theorems, and each must get its own warning. Section two contains a def and
must stay silent. The whole-file check of an end-of-file design stays silent
on this file, because the def in section two masks the other sections.

A region closes at its `end` command, so a `#guard_msgs` around each `end`
captures the verdict of the section that the `end` closes. An empty
expectation asserts silence for section two. -/

set_option linter.superfluousExpose true

@[expose] public section

theorem first_section : 1 = 1 := rfl

/--
warning: This `@[expose] public section` contains no declaration that benefits from body exposure. You can safely remove the `@[expose]` modifier: it only affects `def` and `inductive` bodies, and no declaration here needs exposure (only theorems, instances, classes, structures, abbrevs, notation, or auto-generated declarations).

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
warning: This `@[expose] public section` contains no declaration that benefits from body exposure. You can safely remove the `@[expose]` modifier: it only affects `def` and `inductive` bodies, and no declaration here needs exposure (only theorems, instances, classes, structures, abbrevs, notation, or auto-generated declarations).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
