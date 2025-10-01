import Lean.Meta.PPGoal

namespace Lean.Meta

def ppGoalType (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
  let typeFmt ← ppExpr (← instantiateMVars mvarDecl.type)
  return getGoalPrefix mvarDecl ++ Format.nest 2 typeFmt

end Lean.Meta
