/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true
set_option warn.classDefReducibility false

/-! Negative case: a `def` that carries `@[instance]`, once plain and once behind `open … in`.
Lean exposes the body of an `instance` in every public section, but a `def` keeps the exposure
rules of a `def` whatever attribute it carries: the section modifier controls its body, and the
`rfl` proofs below read it. Each section holds one such def, so each classification runs. The
linter must not fire. -/

namespace SuperfluousExposeTest.InstanceAttrDef

public class Op (α : Type) where op : α → α

@[expose] public section

@[instance] def opNat : Op Nat := ⟨fun n => n + 1⟩

theorem op_three : Op.op (3 : Nat) = 4 := rfl

end

@[expose] public section

open Nat in
@[instance] def opBool : Op Bool := ⟨not⟩

theorem op_true : Op.op true = false := rfl

end

end SuperfluousExposeTest.InstanceAttrDef
