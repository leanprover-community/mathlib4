/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

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
-- Expected: linter warning at end-of-file.
