import Lean

open Lean Elab Tactic Meta

/-- `synthesizeUsing type tac` synthesizes an element of `type` using tactic `tac` -/
-- In Lean3 this was called `solve_aux`,
-- and took a `TacticM α` and captured the produced value in `α`.
-- As this was barely used, we've simplified here.
def synthesizeUsing (type : Expr) (tac : TacticM Unit) : TermElabM Expr := do
  let m ← mkFreshExprMVar type
  let _ ← run m.mvarId! tac
  instantiateMVars m
