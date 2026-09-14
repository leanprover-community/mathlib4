/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: a class and an instance. The projections of the class
follow the visibility of the class, and Lean settles the exposure of an
`instance` without the modifier. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.ClassOnly

class Foo (α : Type) where
  triv : True

instance instFooNat : Foo Nat := ⟨trivial⟩

theorem use_foo [Foo Nat] : True := trivial

end SuperfluousExposeTest.ClassOnly

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
