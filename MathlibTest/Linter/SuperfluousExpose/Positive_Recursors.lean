/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! @[expose] public section --/

/-! Positive case: `structure` produces an auto-generated `.rec`, `.recOn`,
`.casesOn`, and projection defs. None are exposure-relevant. Linter must fire. -/
@[expose] public section

namespace SuperfluousExposeTest.Recursors

structure Point where
  x : Nat
  y : Nat

theorem point_zero_zero : (⟨0, 0⟩ : Point).x = 0 := rfl

end SuperfluousExposeTest.Recursors
-- Expected: linter warning at end-of-file.
