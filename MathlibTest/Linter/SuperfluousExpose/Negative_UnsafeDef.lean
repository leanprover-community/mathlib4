/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains an `unsafe def`. Lean treats it as a
`def` for exposure, so the section modifier controls its body. Downstream
`unsafe` code can still prove `rfl` facts about it, and a hidden body breaks
those proofs. The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.UnsafeDef

unsafe def unsafeOp : Nat → Nat := fun n => n + 1

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.UnsafeDef
-- Expected: no linter warning.
