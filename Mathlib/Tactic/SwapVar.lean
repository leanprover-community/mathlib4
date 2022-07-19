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
elab "swap_var " vars:(colGt (ident " ↔ "? ident)),+ : tactic =>
  liftMetaTactic fun mvarId => do
    let mut ctx ← getLCtx
    for stx in vars.getElems do
      let getDecl (stx : Syntax) :=
        match ctx.findFromUserName? stx.getId with
        | some decl => pure (stx.getId, decl.fvarId)
        | none => throwErrorAt stx "swap_var: unknown variable {stx.getId}"
      let (n1, fvar1) ← getDecl stx.raw[0]
      let (n2, fvar2) ← getDecl stx.raw[2]
      ctx := ctx.setUserName fvar1 n2
      ctx := ctx.setUserName fvar2 n1
    let mvarIdNew ← mkFreshExprMVarAt ctx (← getLocalInstances) (← getMVarType mvarId)
      .syntheticOpaque (← getMVarTag mvarId)
    assignExprMVar mvarId mvarIdNew
    return [mvarIdNew.mvarId!]
