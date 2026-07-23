/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: `scoped instance`. Same situation as `local instance` —
`isInstanceCore` misses it, and there is no robust signal we can use to
distinguish it from an `@[implicit_reducible] def` non-instance shortcut.
The linter conservatively stays silent. -/

@[expose] public section

namespace SuperfluousExposeTest.ScopedInstance

class Foo (α : Type) where dummy : Unit

scoped instance instFooNat : Foo Nat := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ScopedInstance
-- Expected: NO linter warning.
