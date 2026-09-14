/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: a class, a `local instance`, and a theorem. The linter
classifies a declaration at the command that creates it, while the instance
is still active, so `Lean.Meta.isInstanceCore` identifies the local
instance. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.LocalInstance

class Tagged (α : Type) where dummy : Unit

local instance instTaggedNat : Tagged Nat := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.LocalInstance

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
