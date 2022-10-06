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
`synthesizeUsing type tac` synthesizes an element of `type` using tactic `tac`.

The tactic `tac` may leave goals open, these remain as metavariables in the returned expression.
-/
-- In Lean3 this was called `solve_aux`,
-- and took a `TacticM α` and captured the produced value in `α`.
-- As this was barely used, we've simplified here.
def synthesizeUsing (type : Expr) (tac : TacticM Unit) : TermElabM Expr := do
  let m ← mkFreshExprMVar type
  let _ ← run m.mvarId! tac
  instantiateMVars m
