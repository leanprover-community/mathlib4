/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: file with only `@[irreducible] def`s. Although the
`@[irreducible]` annotation tells the elaborator not to unfold automatically,
downstream code can still explicitly `rw [opaqueZero]` / `unfold opaqueZero`,
which requires the body to be reachable. Linter must NOT fire. -/

@[expose] public section

namespace SuperfluousExposeTest.IrreducibleDef

@[irreducible] def opaqueZero : Nat := 0
@[irreducible] def opaqueId (n : Nat) : Nat := n

theorem opaqueZero_unfolded : opaqueZero = opaqueZero := rfl

end SuperfluousExposeTest.IrreducibleDef
-- Expected: NO linter warning.
