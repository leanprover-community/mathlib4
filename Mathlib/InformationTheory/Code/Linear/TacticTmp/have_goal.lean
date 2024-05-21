import Lean

open Lean Elab Command Term Meta Tactic

-- elab "my_exact " v:term : tactic => Lean.Elab.Tactic.withMainContext do
--   -- let goal ← Lean.Elab.Tactic.getMainGoal
--   -- let goalType ← Lean.Elab.Tactic.getMainTarget
--   Lean.Elab.Tactic.evalTactic (← `(tactic| exact $v)  )

--   -- Lean.Elab.Tactic.closeMainGoal pr

elab "have_goal " n:ident " := " v:term : tactic => withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType -- get the goal mvar and type
  evalTactic (← `(tactic| exact $v)) -- close the goal using the provided term
  let pr ← instantiateMVars (Expr.mvar goal) -- grab the reduced form of the provided term
  let goals : List Lean.MVarId ← getGoals
  let newGoals ← goals.mapM fun mvarId => do -- for each remaining goal,
    mvarId.withContext do
      let lctx ← getLCtx
      if ← MetavarContext.isWellFormed lctx goalType then
        if ← MetavarContext.isWellFormed lctx pr then -- check if the provided term and goal type are valid
          let mvarIdNew ← mvarId.assert n.getId goalType pr
          let (_, mvarIdNew) ← mvarIdNew.intro1P -- if so, add the term and type under the given name
          return mvarIdNew
        else return mvarId -- otherwise, do nothing
      else return mvarId
  setGoals newGoals -- put back the goals

elab "skip_goal" : tactic => Lean.Elab.Tactic.withMainContext do
  let goals ← Lean.Elab.Tactic.getGoals
  match goals with
    | [] => return
    | g::goalss => Lean.Elab.Tactic.setGoals (goalss.append [g])


elab "have_goal' " n:ident " := " v:term : tactic => Tactic.withMainContext do
  let goalType ← getMainTarget
  let pr ← Tactic.elabTermEnsuringType v goalType
  closeMainGoal pr
  let newGoals ← (← getGoals).mapM fun mvarId => mvarId.withContext do
    let lctx ← getLCtx
    let goaltype_welformed ← MetavarContext.isWellFormed lctx pr
    let expr_welformed ← MetavarContext.isWellFormed lctx pr
    if goaltype_welformed ∧ expr_welformed then
      let mvarIdNew ← mvarId.assert n.getId goalType pr
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return mvarIdNew
    else return mvarId
  setGoals newGoals

elab "have_goal'' " n:ident " := " v:term : tactic => withMainContext do
  let mvarId :: goals ← getUnsolvedGoals | throwNoGoalsToBeSolved
  let goalType ← mvarId.getType
  let (pr, prGoals) ← elabTermWithHoles v goalType `goal
  unless ← occursCheck mvarId pr do throwError "\
    'have_goal' tactic failed, value{indentExpr pr}\n\
    depends on main goal metavariable {mkMVar mvarId}"
  mvarId.assign pr
  let newGoals ← goals.mapM fun mvarId => mvarId.withContext do
    let lctx ← getLCtx
    if ← (MetavarContext.isWellFormed lctx goalType <&&> MetavarContext.isWellFormed lctx pr) then
      let mvarIdNew ← mvarId.assert n.getId goalType pr
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return mvarIdNew
    else return mvarId
  setGoals (prGoals ++ newGoals)
