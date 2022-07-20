/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Util.Tactic

namespace Mathlib.Tactic

/-- The parser for swap rules -/
syntax swapRule := ident " ↔ "? ident

/--
`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A *swap_rule* is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```
-/
elab "swap_var " vars:(colGt swapRule),+ : tactic =>
  modifyLocalContext fun ctx =>
    vars.getElems.foldlM (init := ctx) fun ctx stx => do
      let `(swapRule| $n₁:ident $[↔]? $n₂:ident) := stx | unreachable!
      let (n₁, fvarId₁) ← getNameAndFVarId ctx n₁
      let (n₂, fvarId₂) ← getNameAndFVarId ctx n₂
      pure $ ctx.setUserName fvarId₁ n₂ |>.setUserName fvarId₂ n₁
