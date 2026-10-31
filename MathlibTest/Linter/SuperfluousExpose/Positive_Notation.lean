/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: only `notation` and `infix` declarations. Lean hides the body of a generated
parser descriptor in every public section. The linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Notation

class Op (α : Type) where op : α → α → α

notation "OP[" a ", " b "]" => Op.op a b
infixl:65 " ⋄ " => Op.op

theorem op_eq (a : Nat) [Op Nat] : OP[a, a] = a ⋄ a := rfl

end SuperfluousExposeTest.Notation

/--
warning: This `@[expose] public section` contains no declaration that benefits from exposure. You can safely remove the `@[expose]` modifier: it only changes the bodies of `def` declarations, and no `def` here needs its body downstream.

Note: This linter can be disabled with `set_option linter.superfluousExpose false`
-/
#guard_msgs in
end
