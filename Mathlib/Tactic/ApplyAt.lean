import Mathlib.Tactic
import Lean

namespace Mathlib.Tactic
open Lean Meta Elab Tactic Term

example {α β γ : Type*} (f : α → β) : True := by
  run_tac withMainContext do
    let some ldecl := (← getLCtx).findFromUserName? `f | unreachable!
    let (mvs,bis,tf) ← forallMetaTelescopeReducing ldecl.type (some 1)
    let mvarid ← getMainGoal
    let mvarid ← mvarid.assert ldecl.userName tf (.app ldecl.toExpr mvs[0]!)
    let (_, mvarid) ← mvarid.intro1P
    let mvarid ← mvarid.tryClear ldecl.fvarId
    replaceMainGoal <| [mvarid] ++ mvs.toList.map fun e => e.mvarId!
  sorry
