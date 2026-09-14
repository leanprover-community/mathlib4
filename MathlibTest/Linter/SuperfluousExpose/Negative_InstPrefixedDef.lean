/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: a plain `def` whose name starts with `inst` and an
uppercase letter, and whose return type is not a class. The linter
identifies an instance with `Lean.Meta.isInstanceCore` rather than by name,
so `instCustom` counts as a plain def whose body matters downstream. The
linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.InstPrefixedDef

def instCustom : Nat := 42

theorem instCustom_eq : instCustom = 42 := rfl

end SuperfluousExposeTest.InstPrefixedDef
