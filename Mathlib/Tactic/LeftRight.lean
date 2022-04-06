import Lean
import Lean.Meta
import Lean.Elab

namespace Mathlib.Tactic.Left
open Lean Meta Elab
open Tactic
def leftMeta (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `left
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        unless ival.ctors.length == 2 do
          throwTacticEx `constructor mvarId "left target applies for inductive types with exactly two constructors"
        let ctor := ival.ctors.toArray[0]
        try
          return ← apply mvarId (Lean.mkConst ctor us)
        catch _ =>
          pure ()
        throwTacticEx `constructor mvarId "no applicable constructor found"

elab "left" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic <| fun mvarId => leftMeta mvarId

end Left

namespace Mathlib.Tactic.Right
open Lean Meta Elab
open Tactic
def rightMeta (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `left
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `constructor mvarId "target is not an inductive datatype")
      fun ival us => do
        unless ival.ctors.length == 2 do
          throwTacticEx `constructor mvarId "left target applies for inductive types with exactly two constructors"
        let ctor := ival.ctors.toArray[1]
        try
          return ← apply mvarId (Lean.mkConst ctor us)
        catch _ =>
          pure ()
        throwTacticEx `constructor mvarId "no applicable constructor found"

elab "right" : tactic => do
  Lean.Elab.Tactic.liftMetaTactic <| fun mvarId => rightMeta mvarId

end Right
