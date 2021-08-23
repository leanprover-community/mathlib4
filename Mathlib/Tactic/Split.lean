/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
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

elab "split" : tactic => withMainContext do
  let mvarIds' ← Meta.split (← getMainGoal)
  Term.synthesizeSyntheticMVarsNoPostponing
  replaceMainGoal mvarIds'

-- TODO: we can't implement `fsplit`
-- until the TODO in `Lean.Meta.apply` (in core) for `ApplyNewGoals` is completed.

end Tactic
end Lean.Elab
