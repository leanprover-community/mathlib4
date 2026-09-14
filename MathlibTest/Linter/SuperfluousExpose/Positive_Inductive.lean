/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: an `inductive` that is not a structure. The type, its
constructors and its recursors follow the visibility of the declaration, so
downstream pattern matching works without the modifier. The linter must
fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Inductive

inductive Tree (α : Type)
  | leaf
  | node : Tree α → α → Tree α → Tree α

theorem leaf_eq : (Tree.leaf : Tree Nat) = Tree.leaf := rfl

end SuperfluousExposeTest.Inductive

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
