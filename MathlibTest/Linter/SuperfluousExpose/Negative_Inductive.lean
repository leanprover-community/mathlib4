/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: the file contains an `inductive` that is not a structure
or a class. Downstream pattern matching needs access to the constructors.
The linter must not fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Inductive

inductive Tree (α : Type)
  | leaf
  | node : Tree α → α → Tree α → Tree α

theorem leaf_eq : (Tree.leaf : Tree Nat) = Tree.leaf := rfl

end SuperfluousExposeTest.Inductive
-- Expected: no linter warning.
