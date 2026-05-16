/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import all Mathlib.Tactic.Linter.SuperfluousExpose
import Lean.Elab.Command

open Lean

/-! Positive case: file with only `unsafe def`. Per the Lean reference,
`unsafe` exempts the def from kernel checking; the kernel never reduces
its body. Downstream Lean proofs can never `rw`/`unfold`/`rfl`-through
an unsafe def, so its body's `.olean` placement doesn't affect downstream
typechecking. (Compiled bytecode/IR lives outside the `@[expose]` partition.) -/

@[expose] public section

namespace SuperfluousExposeTest.UnsafeDef

unsafe def unsafeOp : Nat → Nat := fun n => n + 1

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.UnsafeDef

-- Run the linter on artificial `eoi` syntax so we can guard the message.
set_option linter.superfluousExpose true in
open Mathlib.Linter Parser in
/--
warning: This module has `@[expose] public section` but no declaration that would benefit from body exposure. The `@[expose]` modifier can be safely removed: it would only affect `def`/`inductive` bodies, and there are none here that need exposure (only theorems, instances, classes/structures, abbrevs, notation, or auto-generated decls).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
run_cmd do
  let eoi := mkNode ``Command.eoi #[mkAtom .none ""]
  superfluousExpose.run eoi
