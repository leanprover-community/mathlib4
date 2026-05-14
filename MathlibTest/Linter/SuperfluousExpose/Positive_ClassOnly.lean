/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: `class` declaration + instance — both have auto-generated
projection/witness defs, but they're not "exposure-relevant". Linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ClassOnly

class Foo (α : Type) where
  triv : True

instance instFooNat : Foo Nat := ⟨trivial⟩

theorem use_foo (a : Nat) (_ : Foo a.succ.succ) : True := trivial

end SuperfluousExposeTest.ClassOnly
-- Expected: linter warning at end-of-file.
