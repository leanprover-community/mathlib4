import Lean.Meta.Tactic.Apply
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

def Lean.Meta.split (mvarId : MVarId) : MetaM (List MVarId) := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `split
    let target ← getMVarType' mvarId
    matchConstInduct target.getAppFn
      (fun _ => throwTacticEx `split mvarId "target is not an inductive datatype")
      fun ival us => do
        match ival.ctors with
        | [ctor] => apply mvarId (mkConst ctor us)
        | _ => throwError "split failed, goal must be an inductive type with only one constructor {indentExpr target}"

namespace Lean.Elab
namespace Tactic
open Meta

syntax (name := split) "split" : tactic

@[tactic split] def evalSplit : Tactic := fun _ =>
  withMainContext do
    let mvarIds'  ← Meta.split (← getMainGoal)
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

end Tactic
end Lean.Elab
