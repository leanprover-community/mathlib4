/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: file with only `abbrev`s. In modules, bodies of `abbrev`
declarations are exposed by default regardless of `@[expose]`, so the
`@[expose]` is superfluous on an abbrev-only section. -/

@[expose] public section

namespace SuperfluousExposeTest.AbbrevOnly

abbrev MyNat := Nat
abbrev double (n : Nat) : Nat := n + n

theorem double_zero : double 0 = 0 := rfl

end SuperfluousExposeTest.AbbrevOnly
-- Expected: linter warning at end-of-file.
