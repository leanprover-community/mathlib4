/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Init
import Mathlib.Tactic.Linter.SuperfluousExpose

/-! Positive case: only a `notation` declaration. It creates a `term…` def
whose body is a parser descriptor, and Lean reads that descriptor through
its compiled code. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Notation

class Op (α : Type) where op : α → α → α

notation "OP[" a ", " b "]" => Op.op a b

theorem op_eq (a : Nat) [Op Nat] : OP[a, a] = Op.op a a := rfl

end SuperfluousExposeTest.Notation

set_option linter.superfluousExpose true in
/--
warning: using 'exit' to interrupt Lean
---
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
#exit
