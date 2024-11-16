import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic

open Qq Lean Elab Meta Tactic

inductive CompareResult (x : Q(Real))
| pos (pf : Q(0 < $x))
| neg (pf : Q($x < 0))
| zero (pf : Q($x = 0))

-- Isn't optimal. May be can avoid `evalTacticAt`, and `TacticM`
def compareReal (x : Q(Real)) : TacticM (CompareResult x) := do
  let g := q(0 < $x)
  let e ← mkFreshExprMVar g
  let res ← evalTacticAt (← `(tactic| norm_num)) e.mvarId!
  if res.isEmpty then
    return .pos e

  let g := q($x < 0)
  let e ← mkFreshExprMVar g
  let res ← evalTacticAt (← `(tactic| norm_num)) e.mvarId!
  if res.isEmpty then
    return .neg e

  let g := q($x = 0)
  let e ← mkFreshExprMVar g
  let res ← evalTacticAt (← `(tactic| norm_num)) e.mvarId!
  if res.isEmpty then
    return .zero e
  throwError f!"Cannot compare real number {← ppExpr x} with zero"
