import Lean
import Lean.Meta
import Lean.Elab

namespace Mathlib.Tactic.LeftRight
open Lean Meta Elab
open Tactic
def leftRightMeta (pickLeft: Bool)(mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `left
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        unless ival.ctors.length == 2 do
          throwTacticEx `constructor mvarId "left target applies for inductive types with exactly two constructors"
        let ctor :=
          if pickLeft then ival.ctors.toArray[0]
          else ival.ctors.toArray[1]
        try
          return ← apply mvarId (Lean.mkConst ctor us)
        catch _ =>
          pure ()
        throwTacticEx `constructor mvarId "no applicable constructor found"

end LeftRight

open LeftRight
namespace Mathlib.Tactic.Left

elab "left" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic <| fun mvarId => leftRightMeta true mvarId

end Left
namespace Mathlib.Tactic.Right

elab "right" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic <| fun mvarId => leftRightMeta false mvarId

end Right
