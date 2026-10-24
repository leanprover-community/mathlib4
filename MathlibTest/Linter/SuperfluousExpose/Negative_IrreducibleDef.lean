/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: only `@[irreducible] def`s. The attribute stops the elaborator from unfolding
the def on its own, but downstream code writes `rw [opaqueZero]` or `unfold opaqueZero`, which
read the body. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.IrreducibleDef

@[irreducible] def opaqueZero : Nat := 0
@[irreducible] def opaqueId (n : Nat) : Nat := n

theorem opaqueZero_unfolded : opaqueZero = opaqueZero := rfl

end SuperfluousExposeTest.IrreducibleDef
