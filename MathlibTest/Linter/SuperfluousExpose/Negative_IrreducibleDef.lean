/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains only `@[irreducible] def`s. The
`@[irreducible]` attribute tells the elaborator to not unfold the def
automatically. But downstream code can still write `rw [opaqueZero]` or
`unfold opaqueZero`, and these need the body. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.IrreducibleDef

@[irreducible] def opaqueZero : Nat := 0
@[irreducible] def opaqueId (n : Nat) : Nat := n

theorem opaqueZero_unfolded : opaqueZero = opaqueZero := rfl

end SuperfluousExposeTest.IrreducibleDef
-- Expected: no linter warning.
