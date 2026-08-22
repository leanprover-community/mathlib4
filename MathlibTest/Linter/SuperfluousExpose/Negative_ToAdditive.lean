/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose
public import Mathlib.Tactic.Translate.ToAdditive

set_option linter.superfluousExpose true

/-! Negative case: the file contains a `@[to_additive]` def. The source def
is a real def, and the auto-generated additive twin is also a real def with
a body that matters. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ToAdditive

@[to_additive mySum]
def myProduct (x y : Nat) : Nat := x * y

theorem myProduct_one_one : myProduct 1 1 = 1 := rfl

end SuperfluousExposeTest.ToAdditive
-- Expected: no linter warning. Both `myProduct` and the derived `mySum` are
-- real defs that benefit from exposure.
