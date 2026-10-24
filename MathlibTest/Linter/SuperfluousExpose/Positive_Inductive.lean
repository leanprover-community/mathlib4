/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: an `inductive` that is not a structure. The type, its constructors and its
recursors have no body, and its generated auxiliaries are auto-declarations. The linter must
fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Inductive

inductive Tree (α : Type)
  | leaf
  | node : Tree α → α → Tree α → Tree α

theorem leaf_eq : (Tree.leaf : Tree Nat) = Tree.leaf := rfl

end SuperfluousExposeTest.Inductive

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
