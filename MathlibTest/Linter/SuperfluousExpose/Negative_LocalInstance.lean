/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains a `local instance`.
`Lean.Meta.isInstanceCore` does not see it, because the instance is scoped to
its namespace. No robust signal can recover it: in the environment, a `local
instance` looks identical to an `@[implicit_reducible] def` shortcut that is
not an instance. The linter stays silent to be conservative. -/

@[expose] public section

namespace SuperfluousExposeTest.LocalInstance

class Tagged (α : Type) where dummy : Unit

local instance instTaggedNat : Tagged Nat := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.LocalInstance
-- Expected: no linter warning.
