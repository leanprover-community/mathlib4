/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: only a `partial def`. Lean records it as an `opaqueInfo`,
and the kernel treats it as an opaque constant, so downstream typechecking
cannot read the body. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.PartialDef

partial def loopWhile (n : Nat) : Nat :=
  if n = 0 then 0 else loopWhile (n - 1)

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.PartialDef

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
