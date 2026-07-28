/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains a `scoped instance`. The situation is
the same as for `local instance`: `isInstanceCore` does not see it, and no
robust signal can distinguish it from an `@[implicit_reducible] def` shortcut
that is not an instance. The linter stays silent to be conservative. -/

@[expose] public section

namespace SuperfluousExposeTest.ScopedInstance

class Foo (α : Type) where dummy : Unit

scoped instance instFooNat : Foo Nat := ⟨()⟩

theorem trivial_proof : True := trivial

end SuperfluousExposeTest.ScopedInstance
-- Expected: no linter warning.
