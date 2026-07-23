/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose
public import Mathlib.Tactic.Translate.ToAdditive

set_option linter.superfluousExpose true

/-! Negative case: `@[to_additive]` def. The source `def` is real; the
auto-generated additive twin is also a real def with body matter. Linter
must NOT fire on either the source-file or its derived-translation file. -/

@[expose] public section

namespace SuperfluousExposeTest.ToAdditive

@[to_additive mySum]
def myProduct (x y : Nat) : Nat := x * y

theorem myProduct_one_one : myProduct 1 1 = 1 := rfl

end SuperfluousExposeTest.ToAdditive
-- Expected: NO linter warning (both `myProduct` (def) and its `to_additive`-derived
-- `mySum` are real defs that benefit from exposure).
