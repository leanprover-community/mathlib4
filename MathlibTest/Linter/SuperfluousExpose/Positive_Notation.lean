/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: the file contains only a `notation` declaration. A notation
declaration creates a `term…` def in the environment. Its body is a syntax
tree, and downstream code never unfolds it. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Notation

class Op (α : Type) where op : α → α → α

notation "OP[" a ", " b "]" => Op.op a b

theorem op_eq (a : Nat) [Op Nat] : OP[a, a] = Op.op a a := rfl

end SuperfluousExposeTest.Notation

-- `#exit` is a terminal command, so the linter fires there and `#guard_msgs`
-- can capture the warning. The linter option is off at the real end of the
-- file, so the linter is silent there.
set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This module has `@[expose] public section` but no declaration that would benefit from body exposure. The `@[expose]` modifier can be safely removed: it would only affect `def`/`inductive` bodies, and there are none here that need exposure (only theorems, instances, classes/structures, abbrevs, notation, or auto-generated decls).

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
