/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, David Renshaw
-/
import Lean
import Mathlib.Init.Logic
import Mathlib.Tactic.SplitIfsAttr

/-!
Tactic to split if-then-else expressions.
-/

namespace Mathlib.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

attribute [split_ifs_reduction] if_pos if_neg dif_pos dif_neg if_congr

/-- Simulates the `all_goals` tactic combinator.
-/
private def evalAllGoals : TacticM Unit → TacticM Unit := fun tac => do
  let mvarIds ← getGoals
  let mut mvarIdsNew := #[]
  for mvarId in mvarIds do
    unless (← mvarId.isAssigned) do
      setGoals [mvarId]
      try
        tac
        mvarIdsNew := mvarIdsNew ++ (← getUnsolvedGoals)
      catch ex =>
        if (← read).recover then
          Elab.logException ex
          mvarIdsNew := mvarIdsNew.push mvarId
        else
          throw ex
  setGoals mvarIdsNew.toList

/-- Simulates the `<;>` tactic combinator.
-/
private def tac_and_then : TacticM Unit → TacticM Unit → TacticM Unit :=
fun tac1 tac2 => focus do
  tac1
  evalAllGoals tac2

/-- Finds an if-then-else and returns its condition.
-/
private partial def findIfCond? (e : Expr) : Option Expr :=
  go e
where
  go (e : Expr) : Option Expr :=
    if let some ifCond := e.find? isCandidate then
        let cond := ifCond.getArg! 1 5
        -- Try to find a nested `if` in `cond`
        go cond |>.getD cond
    else
      none

  isCandidate (e : Expr) : Bool := Id.run do
    if e.isIte || e.isDIte then
      !(e.getArg! 1 5).hasLooseBVars
    else
      false

private def get_relevant_fvarids_of_loc (loc : Location) : TacticM (List FVarId) :=
match loc with
| Location.wildcard => do
   let lctx ← getLCtx
   return lctx.getFVarIds.toList
| Location.targets hyps _ => do
   let fvarIds ← hyps.mapM getFVarId
   return fvarIds.toList

/-- Returns `true` if `loc` includes the goal's target.
-/
private def loc_includes_target (loc : Location) : Bool :=
match loc with
| Location.wildcard => true
| Location.targets _ tgt => tgt

/-- Finds an if condition to split.
-/
private def find_if_cond_at (loc : Location) : TacticM (Option Expr) := do
   let fvarIds ← get_relevant_fvarids_of_loc loc
   let hTypes ← ((fvarIds.map mkFVar).mapM inferType : MetaM _)
   let hTypes ← hTypes.mapM instantiateMVars
   let tgt ← getMainTarget
   let es := if loc_includes_target loc then tgt::hTypes else hTypes
   for e in es do
     if let some cond := findIfCond? e
     then return some cond
   return none

/-- Discharges `¬¬p` using `h : p`.
-/
private def dischargeUsingNotNotIntro? (e : Expr) : SimpM (Option Expr) :=
  if e.isAppOf `Not && e.getAppArgs[0]!.isAppOf `Not
  then do
    let eInner := e.getAppArgs[0]!.getAppArgs[0]!
    (← getLCtx).findDeclRevM? fun localDecl => do
      if localDecl.isImplementationDetail then
        return none
      else if (← isDefEq eInner localDecl.type) then
        return some (mkApp (mkApp (mkConst `not_not_intro) localDecl.type) localDecl.toExpr)
      else
        return none
  else pure none

/-- `Simp.Discharge` strategy to use in `reduceIfsAt`.
-/
private def discharger (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← Simp.dischargeUsingAssumption? e
    then return some e1
  if let some e2 ← dischargeUsingNotNotIntro? e
    then return some e2
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/-- Simplifies if-then-else expressions after cases have been split out.
-/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let some ext ← getSimpExtension? `split_ifs_reduction | return
  let thms ← ext.getTheorems
  let ctx : Simp.Context := { simpTheorems := #[thms] }
  let _ ← simpLocation ctx discharger loc
  pure ()

/-- Splits a single if-then-else expression and then reduces the resulting goals.
-/
private def splitIf1 (cond: Expr) (hName : Name) (loc : Location) : TacticM Unit := do
  let splitCases := liftMetaTactic fun mvarId => do
    let (s1, s2) ← mvarId.byCases cond hName
    pure [s1.mvarId, s2.mvarId]
  tac_and_then splitCases (reduceIfsAt loc)

/-- Pops of the front of the list of names, or generates a fresh name if the
list is empty.
-/
private def getNextName (hNames: IO.Ref (List Name)) : MetaM Name := do
  match ←hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns; pure n

/-- Returns `true` if the condition or its negation already appears as a hypothesis.
-/
private def valueKnown (cond : Expr) : TacticM Bool := do
  let lctx ← getLCtx
  let fvarIds := lctx.getFVarIds
  let hTypes ← ((fvarIds.map mkFVar).mapM inferType : MetaM _)
  let hTypes := hTypes.toList
  let not_cond := mkApp (mkConst `Not) cond
  return (hTypes.contains cond) || (hTypes.contains not_cond)

/-- Main loop of split_ifs. Pulls names for new hypotheses from `hNames`.
Stops if it encounters a condition in the passed-in `List Expr`.
-/
private partial def splitIfsCore (loc : Location) (hNames : IO.Ref (List Name)) :
  List Expr → TacticM Unit := fun done => do
  let some cond ← find_if_cond_at loc
      | Meta.throwTacticEx `split_ifs (←getMainGoal) "no if-the-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    tac_and_then (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    tac_and_then (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|> pure ())

/-- Splits all if-then-else-expressions into multiple goals.
Given a goal of the form `g (if p then x else y)`, `split_ifs` will produce
two goals: `p ⊢ g x` and `¬p ⊢ g y`.
If there are multiple ite-expressions, then `split_ifs` will split them all,
starting with a top-most one whose condition does not contain another
ite-expression.
`split_ifs at *` splits all ite-expressions in all hypotheses as well as the goal.
`split_ifs with h₁ h₂ h₃` overrides the default names for the hypotheses.
-/
syntax (name := splitIfs) "split_ifs" (ppSpace location)? (" with " (colGt binderIdent)+)? : tactic

elab_rules : tactic
| `(tactic| split_ifs $[$loc:location]? $[with $withArg*]?) =>
  let loc := match loc with
  | none => Location.targets #[] true
  | some loc => expandLocation loc
  let names := match withArg with
  | none => []
  | some args => args.map (λ s => if let `(binderIdent| $x:ident) := s
                                  then x.getId
                                  else `x) |>.toList
  withMainContext do
    let names ← IO.mkRef names
    splitIfsCore loc names []
