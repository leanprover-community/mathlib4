import Lean
import Mathlib.Lean.Elab.Tactic.Basic

open Lean Elab Tactic Meta

/-- `solve_aux' type tac` synthesizes an element of `type` using tactic `tac`,
additionally capturing the return value of `tac`. -/
def solve_aux' {α : Type} (type : Expr) (tac : TacticM α) : TermElabM (α × Expr) := do
  let m ← mkFreshExprMVar type
  let ⟨some a, _⟩ ← run' m.mvarId! tac | throwError "Auxiliary tactic failed"
  return ⟨a, m⟩

/-- `solve_aux type tac` synthesizes an element of `type` using tactic `tac` -/
def solve_aux (type : Expr) (tac : TacticM Unit) : TermElabM Expr := do
  let m ← mkFreshExprMVar type
  let _ ← run m.mvarId! tac
  return m

  -- Or:
  -- return (←solve_aux' type tac).2


elab "foo" : tactic => do
  closeMainGoal (← solve_aux (mkConst ``Nat) (evalTactic (←`(tactic| constructor))))

example : Nat := by
  foo
