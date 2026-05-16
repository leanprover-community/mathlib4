/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a regular `def` whose name starts with `inst` followed by
an uppercase letter, but whose return type is *not* a class. The
`isAutoInstanceName` leaf-name heuristic alone would match this, but the
type-level guard (`returnTypeIsClass`) prevents the false positive.

The linter must NOT fire — `instCustom` is a regular def whose body matters
downstream. -/

@[expose] public section

namespace SuperfluousExposeTest.InstPrefixedDef

def instCustom : Nat := 42

theorem instCustom_eq : instCustom = 42 := rfl

end SuperfluousExposeTest.InstPrefixedDef
-- Expected: NO linter warning. (Regression test for the `inst[A-Z]…` heuristic.)
