/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean

/-!
# `SynthesizeUsing`

This is a slight simplification of the `solve_aux` tactic in Lean3.
-/

open Lean Elab Tactic Meta

/--
`synthesizeUsing type tac` synthesizes an element of type `type` using tactic `tac`.

The tactic `tac` is allowed to leave goals open, and these remain as metavariables in the
returned expression.
-/
-- In Lean3 this was called `solve_aux`,
-- and took a `TacticM α` and captured the produced value in `α`.
-- As this was barely used, we've simplified here.
def synthesizeUsing (type : Expr) (tac : TacticM Unit) : MetaM (List MVarId × Expr) := do
  let m ← mkFreshExprMVar type
  let goals ← (run m.mvarId! tac).run'
  return (goals, ← instantiateMVars m)

/--
`synthesizeUsing type tac` synthesizes an element of type `type` using tactic `tac`.

The tactic must solve for all goals, in contrast to `synthesizeUsing`.
-/
def synthesizeUsing' (type : Expr) (tac : TacticM Unit) : MetaM Expr := do
  let (_, e) ← synthesizeUsing type (tac *> Tactic.done)
  return e

/--
`synthesizeUsing type tacticSyntax` synthesizes an element of type `type` by evaluating the
given tactic syntax.

Example:
```lean
let (gs, e) ← synthesizeUsing ty (← `(tactic| congr!))
```

The tactic `tac` is allowed to leave goals open, and these remain as metavariables in the
returned expression.
-/
def synthesizeUsingTactic (type : Expr) (tac : Syntax) : MetaM (List MVarId × Expr) := do
  synthesizeUsing type (do evalTactic tac)

/--
`synthesizeUsing' type tacticSyntax` synthesizes an element of type `type` by evaluating the
given tactic syntax.

Example:
```lean
let e ← synthesizeUsing ty (← `(tactic| norm_num))
```

The tactic must solve for all goals, in contrast to `synthesizeUsingTactic`.
-/
def synthesizeUsingTactic' (type : Expr) (tac : Syntax) : MetaM Expr := do
  synthesizeUsing' type (do evalTactic tac)
