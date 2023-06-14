import Std.Data.List.Basic

namespace Mathlib.Tactic.Prune

open Lean Elab Meta Tactic

def revertVarsOnce : TacticM (Array FVarId × List LocalDecl × MVarId) := focus do
  let ctx := (← getLCtx).decls.toList.reduceOption
  let gMVar := ← getMainGoal
  let goal := ← getMainTarget
  let foundDecls := (ctx.map fun x =>
    if (goal.find? (. == x.toExpr)).isSome then some x else none).reduceOption
  let fvarIdFound := (foundDecls.map Lean.LocalDecl.fvarId).toArray
  let (fvs, newGoal) := ← gMVar.revert fvarIdFound
  setGoals [newGoal]
  pure (fvs, ctx, newGoal)

partial
def revertLoop : TacticM (List LocalDecl × MVarId) := focus do
  let (fvars, ctx, newGoal) := ← revertVarsOnce
  if fvars.size == 0 then pure (ctx, newGoal) else revertLoop

def revertNLoop (n m : Nat) : TacticM (List LocalDecl × MVarId) := do
  match n with
  | 0     => revertLoop
  | 1     => do let goal := ← getMainGoal; pure ([], goal)
  | n + 1 => focus do
    let (fvars, ctx, newGoal) := ← revertVarsOnce
    if fvars.size == 0 then
      logInfo m!"{m} iterations suffice.\nTry this: prune {m}"
      pure (ctx, newGoal) else revertNLoop n (m + 1)

def pruneTac : TacticM Unit := focus do
  let dcls := (← getLCtx).decls.toList.reduceOption
  let goal := ← getMainGoal
  let newGoal ← goal.tryClearMany (dcls.map LocalDecl.fvarId).toArray
  setGoals [newGoal]
  let nms := (← getMainTarget).getForallBinderNames
  let (_newfvs, rGoal) := ← introNCore newGoal nms.length [] True True
  setGoals [rGoal]

syntax "prune" (num)? : tactic

elab_rules : tactic
  | `(tactic| prune $[$n]?) => do
    let _ := ← revertNLoop (n.getD default).getNat 0
    pruneTac

end Mathlib.Tactic.Prune
