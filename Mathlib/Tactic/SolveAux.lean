import Lean
import Mathlib.Lean.Elab.Tactic.Basic

open Lean Elab Tactic Meta

/-- `solve_aux type tac` synthesize an element of 'type' using tactic 'tac' -/
def solve_aux {α : Type} (type : Expr) (tac : TacticM α) : TacticM (α × Expr) :=
do let m ← mkFreshExprMVar type
   let gs ← getGoals
   setGoals [m.mvarId!]
   let a ← tac
   setGoals gs
   return (a, m)

/-- `solve_aux type tac` synthesize an element of 'type' using tactic 'tac' -/
def solve_aux' {α : Type} (type : Expr) (tac : TacticM α) : TermElabM (α × Expr) :=
do let m ← mkFreshExprMVar type
   let ⟨some a, _⟩ ← run' m.mvarId! tac | throwError "Auxiliary tactic failed"
   return ⟨a, m⟩
