/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a regular `def` whose name starts with `inst` and an
uppercase letter, but whose return type is not a class. A name heuristic
alone would match it, but the linter uses `Lean.Meta.isInstanceCore`, not
the name. Thus `instCustom` counts as a regular def whose body matters
downstream. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.InstPrefixedDef

def instCustom : Nat := 42

theorem instCustom_eq : instCustom = 42 := rfl

end SuperfluousExposeTest.InstPrefixedDef
-- Expected: no linter warning. This is a regression test for name-based
-- instance detection.
