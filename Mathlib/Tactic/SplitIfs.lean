/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, David Renshaw
-/
import Lean
import Mathlib.Init.Logic
import Mathlib.Tactic.Core

/-!
Tactic to split if-then-else expressions.
-/

namespace Mathlib.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- Simulates the `<;>` tactic combinator.
-/
private def tac_and_then : TacticM Unit → TacticM Unit → TacticM Unit :=
fun tac1 tac2 => focus do
  tac1
  allGoals tac2

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
     if let some cond := SplitIf.findIfToSplit? e
     then return some cond
   return none

/-- `Simp.Discharge` strategy to use in `reduceIfsAt`. Delegates to
`SplitIf.discharge?`, and additionally supports discharging `True`, to
better match the behavior of mathlib3's `split_ifs`.
-/
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← SplitIf.discharge? false e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/-- Simplifies if-then-else expressions after cases have been split out.
-/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let ctx ← SplitIf.getSimpContext
  let _ ← simpLocation ctx discharge? loc
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
