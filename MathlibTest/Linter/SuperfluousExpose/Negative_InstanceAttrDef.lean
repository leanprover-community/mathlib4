/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Mathlib.Tactic.Linter.SuperfluousExpose

set_option linter.superfluousExpose true
set_option warn.classDefReducibility false

/-! Negative case: a `def` that carries `@[instance]`. Lean settles the
exposure of an `instance` declaration on its own, but a `def` keeps the
exposure rules of a `def` whatever attribute it carries. The section
modifier controls this body, and downstream `rfl` proofs read it. The linter
must not fire, so the instance exemption must test the command kind and not
`Lean.Meta.isInstanceCore` alone. -/

@[expose] public section

namespace SuperfluousExposeTest.InstanceAttrDef

class Op (α : Type) where op : α → α

@[instance] def opNat : Op Nat := ⟨fun n => n + 1⟩

theorem op_three : Op.op (3 : Nat) = 4 := rfl

end SuperfluousExposeTest.InstanceAttrDef
