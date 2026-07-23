/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: `local instance`. `Lean.Meta.isInstanceCore` misses these
(they're scoped to the namespace they're declared in), and there is no
robust signal we can use to recover them: a `local instance` looks identical
in the environment to an `@[implicit_reducible] def` non-instance shortcut.
The linter conservatively stays silent. -/

@[expose] public section

namespace SuperfluousExposeTest.LocalInstance

class Tagged (α : Type) where dummy : Unit

local instance instTaggedNat : Tagged Nat := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.LocalInstance
-- Expected: NO linter warning.
