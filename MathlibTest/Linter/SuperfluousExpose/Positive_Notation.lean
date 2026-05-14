/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true

/-! Positive case: `notation` only. Notation declarations create `term_…` defs
in the env; those bodies are syntax trees, never `unfold`ed. Linter must fire. -/

@[expose] public section

namespace SuperfluousExposeTest.Notation

class Op (α : Type) where op : α → α → α

notation:65 a " ⊕ " b => Op.op a b

theorem op_eq (a : Nat) [Op Nat] : a ⊕ a = Op.op a a := rfl

end SuperfluousExposeTest.Notation
-- Expected: linter warning at end-of-file.
