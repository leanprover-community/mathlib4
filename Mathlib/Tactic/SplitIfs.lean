/-
Copyright (c) 2018 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, David Renshaw
-/
module

public meta import Lean.Elab.Tactic.Location
public meta import Lean.Meta.Tactic.SplitIf
public meta import Lean.Elab.Tactic.Simp
public import Mathlib.Tactic.Core

/-!
Tactic to split if-then-else expressions.
-/

public meta section

namespace Mathlib.Tactic

open Lean Elab.Tactic Parser.Tactic Lean.Meta

/-- A position where a split may apply.
-/
private inductive SplitPosition
| target
| hyp (fvarId: FVarId)

/-- Collects a list of positions pointed to by `loc` and their types.
-/
private def getSplitCandidates (loc : Location) : TacticM (List (SplitPosition × Expr)) :=
match loc with
| Location.wildcard => do
  let candidates ← (← getLCtx).getFVarIds.mapM
    (fun fvarId ↦ do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  pure ((SplitPosition.target, ← getMainTarget) :: candidates.toList)
| Location.targets hyps tgt => do
  let candidates ← (← hyps.mapM getFVarId).mapM
    (fun fvarId ↦ do
      let typ ← instantiateMVars (← inferType (mkFVar fvarId))
      return (SplitPosition.hyp fvarId, typ))
  if tgt
  then return (SplitPosition.target, ← getMainTarget) :: candidates.toList
  else return candidates.toList

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : Option (Expr × Expr) :=
  match e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars with
  | some iteApp =>
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
    findIfToSplit? cond |>.getD (cond, dec)
  | none => none

/-- Finds an if condition to split. If successful, returns the position and the condition.
-/
private def findIfCondAt (loc : Location) : TacticM (Option (SplitPosition × Expr)) := do
  for (pos, e) in (← getSplitCandidates loc) do
    if let some (cond, _) := findIfToSplit? e
    then return some (pos, cond)
  return none

/-- `Simp.Discharge` strategy to use in `reduceIfsAt`. Delegates to
`SplitIf.discharge?`, and additionally supports discharging `True`, to
better match the behavior of mathlib3's `split_ifs`.
-/
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e ← instantiateMVars e
  if let some e1 ← (← SplitIf.mkDischarge? false) e
    then return some e1
  if e.isConstOf `True
    then return some (mkConst `True.intro)
  return none

/-- Simplifies if-then-else expressions after cases have been split out.
-/
private def reduceIfsAt (loc : Location) : TacticM Unit := do
  let ctx ← SplitIf.getSimpContext
  let ctx := ctx.setFailIfUnchanged false
  let _ ← simpLocation ctx (← ({} : Simp.SimprocsArray).add `reduceCtorEq false) discharge? loc
  pure ()

/-- Splits a single if-then-else expression and then reduces the resulting goals.
Has a similar effect as `SplitIf.splitIfTarget?` or `SplitIf.splitIfLocalDecl?` from
core Lean 4. We opt not to use those library functions so that we can better mimic
the behavior of mathlib3's `split_ifs`.
-/
private def splitIf1 (cond : Expr) (hName : Name) (loc : Location) : TacticM Unit := do
  let splitCases :=
    evalTactic (← `(tactic| by_cases $(mkIdent hName) : $(← Elab.Term.exprToSyntax cond)))
  andThenOnSubgoals splitCases (reduceIfsAt loc)

/-- Pops off the front of the list of names, or generates a fresh name if the
list is empty.
-/
private def getNextName (hNames: IO.Ref (List (TSyntax `Lean.binderIdent))) : MetaM Name := do
  match ← hNames.get with
  | [] => mkFreshUserName `h
  | n::ns => do hNames.set ns
                if let `(binderIdent| $x:ident) := n
                then pure x.getId
                else pure `_

/-- Returns `true` if the condition or its negation already appears as a hypothesis.
-/
private def valueKnown (cond : Expr) : TacticM Bool := do
  let not_cond := mkApp (mkConst `Not) cond
  for h in ← getLocalHyps do
    let ty ← instantiateMVars (← inferType h)
    if cond == ty then return true
    if not_cond == ty then return true
  return false

/-- Main loop of `split_ifs`. Pulls names for new hypotheses from `hNames`.
Stops if it encounters a condition in the passed-in `List Expr`.
-/
private partial def splitIfsCore
    (loc : Location)
    (hNames : IO.Ref (List (TSyntax `Lean.binderIdent))) :
    List Expr → TacticM Unit := fun done ↦ withMainContext do
  let some (_,cond) ← findIfCondAt loc
      | Meta.throwTacticEx `split_ifs (← getMainGoal) "no if-then-else conditions to split"

  -- If `cond` is `¬p` then use `p` instead.
  let cond := if cond.isAppOf `Not then cond.getAppArgs[0]! else cond

  if done.contains cond then return ()
  let no_split ← valueKnown cond
  if no_split then
    andThenOnSubgoals (reduceIfsAt loc) (splitIfsCore loc hNames (cond::done) <|> pure ())
  else do
    let hName ← getNextName hNames
    andThenOnSubgoals (splitIf1 cond hName loc) ((splitIfsCore loc hNames (cond::done)) <|>
      pure ())

/-- `split_ifs` splits the main goal in two goals for every if-then-else expression it contains,
by applying excluded middle to the condition. If the goal has the form `g (if p then x else y)`,
`split_ifs` will result in two goals `h✝ : p ⊢ g x` and `h✝ : ¬p ⊢ g y`. If there are multiple
if-then-else expressions, then `split_ifs` will split them all, starting with a top-most one whose
condition does not contain another if-then-else expression.

* `split_ifs with h₁ h₂ h₃` names the introduced hypotheses.
  Note that names are not reused across splits: on a goal of the form
  `⊢ (if p then 1 else 2) + (if q then 3 else 4)`, use `split_ifs with hp hq hq` to name all
  the hypotheses.
* `split_ifs at l` splits the if-then-else expressions at location(s) l.
-/
syntax (name := splitIfs) "split_ifs" (location)? (" with" (ppSpace colGt binderIdent)+)? : tactic

elab_rules : tactic
| `(tactic| split_ifs $[$loc:location]? $[with $withArg*]?) =>
  let loc := match loc with
  | none => Location.targets #[] true
  | some loc => expandLocation loc
  let names := match withArg with
  | none => []
  | some args => args.toList
  withMainContext do
    let names ← IO.mkRef names
    splitIfsCore loc names []
    for name in ← names.get do
      logWarningAt name m!"unused name: {name}"

end Mathlib.Tactic
