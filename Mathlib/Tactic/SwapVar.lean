/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

import Lean

namespace Mathlib.Tactic

open Lean Meta Elab.Tactic

/--
`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A *swap_rule* is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {a b : Nat} (h : a = b) : a = b ∧ a = a := by
  swap_var a ↔ b
-- b a: Nat
-- h: b = a
-- ⊢ b = a ∧ b = b
  swap_var b y, y ↔ x
-- x a: Nat
-- h: x = a
-- ⊢ x = a ∧ x = x
  exact .intro h $ .refl x
```
-/
elab "swap_var " vars:(colGt (ident " ↔ "? ident)),+ : tactic => do
  let vars := vars.getElems.map fun stx =>
    (stx.raw.getArg 0 |>.getId, stx.raw.getArg 2 |>.getId)
  withMainContext do
    let ctx ← getLCtx
    let temp := ctx.getUnusedName `__h
    let ctxNew := vars.foldl (init := ctx) fun acc pair =>
      acc.renameUserName pair.1 temp
        |>.renameUserName pair.2 pair.1
        |>.renameUserName temp pair.2
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mkFreshExprMVarAt ctxNew (← getLocalInstances) (← getMVarType mvarId)
        .syntheticOpaque (← getMVarTag mvarId)
      assignExprMVar mvarId mvarIdNew
      return [mvarIdNew.mvarId!]
