/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: the file contains only an `unsafe def`. The Lean reference
says that `unsafe` exempts the def from kernel checking, and the kernel never
reduces its body. Downstream proofs cannot apply `rw`, `unfold`, or `rfl` to
an unsafe def. Thus the location of its body in the `.olean` does not affect
downstream typechecking. The compiled code is outside the `@[expose]`
partition. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.UnsafeDef

unsafe def unsafeOp : Nat → Nat := fun n => n + 1

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.UnsafeDef

-- `#exit` is a terminal command, so the linter fires there and `#guard_msgs`
-- can capture the warning. The linter option is off at the real end of the
-- file, so the linter is silent there.
set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This module has `@[expose] public section` but no declaration that would benefit from body exposure. The `@[expose]` modifier can be safely removed: it would only affect `def`/`inductive` bodies, and there are none here that need exposure (only theorems, instances, classes/structures, abbrevs, notation, or auto-generated decls).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
