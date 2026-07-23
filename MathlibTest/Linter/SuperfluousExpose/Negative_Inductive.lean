/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Negative case: file contains a real `inductive` (not a `structure`/`class`).
Downstream pattern-matching needs the constructors exposed. Linter must NOT fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Inductive

inductive Tree (α : Type)
  | leaf
  | node : Tree α → α → Tree α → Tree α

theorem leaf_eq : (Tree.leaf : Tree Nat) = Tree.leaf := rfl

end SuperfluousExposeTest.Inductive
-- Expected: NO linter warning.
