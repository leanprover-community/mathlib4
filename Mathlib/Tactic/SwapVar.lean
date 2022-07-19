/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Mathlib.Tactic.Utils

namespace Mathlib.Tactic

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
elab "swap_var " vars:(colGt (ident " ↔ "? ident)),+ : tactic =>
  modifyLocalContext fun ctx =>
    vars.getElems.foldlM (init := ctx) fun ctx stx => do
      let (n1, fvar1) ← getNameAndFVarId ctx stx.raw[0]
      let (n2, fvar2) ← getNameAndFVarId ctx stx.raw[2]
      pure $ ctx.setUserName fvar1 n2 |>.setUserName fvar2 n1
