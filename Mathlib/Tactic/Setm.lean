/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public meta import Mathlib.Tactic.Core
public meta import Lean.Elab.Tactic.Rewrite

/-!
# The `setm` tactic

This module defines the `setm` tactic.

The `setm` tactic matches a pattern containing named holes to the type of a target, and creates
local declarations for the hole names whose values are the assigned expressions. By default, the
pattern is matched against the goal, but a local declaration can be matched instead via the `using`
syntax.
Optionally, with the syntax `at loc`, it also rewrites at locations `loc` to replace the occurrences
of the matched expressions with the newly-introduced local declarations.

## TODO

It would be nice if the tactic was be made to work for non-constants under binders (by adding forall
binders to the local declarations).
-/

meta section

open Lean Mathlib Elab Tactic Meta Term Syntax

namespace Mathlib.Tactic.SetM

/-- The state updated during replacement of synthetic hole syntax with local declarations. -/
structure SetMReplaceState where
  /-- The modified goal. Invariant: the `FVarId`s in `holes` are in this goal's local context. -/
  goal : MVarId
  /-- Newly created local declaration names for synthetic holes and their fvars. -/
  holes : NameMap FVarId := {}
  /-- New metavariables created for the values of new free variables. We ensure all of these are
    assigned by the end of `setm`, or else log an error. -/
  newMVars : Array MVarId := #[]

abbrev SetMReplaceM := StateT SetMReplaceState TermElabM

/-- Traverse all synthetic holes, creating local declarations for them.

A synthetic hole of the form `?n` leads to a local declaration of the form `n := ?m.1`, with the
new metavariable natural and recorded in the state. -/
def replaceWithLDecls (stx : Syntax) : SetMReplaceM Syntax :=
  stx.replaceM fun stx ↦ do
    let fvar ←
      if let `(?$n:ident) := stx then
        let name := n.getId
        (← get).holes.get? name |>.getDM do
          createLDecl stx name
      else if let `(?_) := stx then
        let name ← mkFreshUserName `x
        createLDecl stx name
      else
        -- Not a synthetic hole.
        return none
    return ← withRef stx <| (← get).goal.withContext <| Term.exprToSyntax (.fvar fvar)
  where
    createLDecl stx name : SetMReplaceM FVarId := do
      let mvar ← mkFreshExprMVar none
      registerMVarErrorCustomInfo mvar.mvarId! stx m!"`{stx}` could not be assigned"
      let goal ← (← get).goal.define name (← mvar.mvarId!.getType) mvar
      let (fvar, goal) ← goal.intro1P
      modify fun s ↦ {
        goal
        holes := s.holes.insert name fvar
        newMVars := s.newMVars.push mvar.mvarId! }
      return fvar

-- TODO: show example! Also check style guide for tactic docstrings
/--
* `setm expr`, where `expr` is a term containing named holes (like `?a`) will match `expr` to the
  current goal and create local declarations assigning the hole names to their inferred value.
  Moreover, it will replace the matches with their new names.
* `setm expr using h` is like `setm expr`, except that `expr` is matched with the local hypothesis
  `h` instead.
* `setm expr (using h)? at loc` is like the above, except that it also rewrites the newly-introduced
  local declarations at the locations `loc`.
-/
syntax (name := setM) "setm " term (" using " ident)? (Parser.Tactic.location)? : tactic

def defeqOrError (goal : MVarId) (p e : Expr) : MetaM Unit :=
  unless ← withReducible <| withAssignableSyntheticOpaque <| isDefEq p e do
    throwTacticEx `setm goal <| MessageData.ofLazyM (es := #[p, e]) do
      let (p, tgt) ← addPPExplicitToExposeDiff p e
      return m!"Pattern{indentExpr p}\nis not definitionally equal \
        to the target{indentExpr tgt}"

/-- Runs `x`, and if `x` throws an exception, rewinds the tactic state *except* for the `InfoState`
and `Messages`. This means that hovers and error messages created within `x` are preserved.

Note: `x` is run under `withSaveInfoContext` in order to propagate hovers and messages correctly.
This means that pre-existing infotrees are not accessible from within `x`. -/
def commitIfNoExPreservingInfoAndMessages {α} (x : TacticM α) : TacticM α := do
  let saved ← saveState
  Tactic.tryCatch (withSaveInfoContext x) fun ex => do
    let saved := { saved with
      term.meta.core.infoState := ← getInfoState
      term.meta.core.messages := (← getThe Core.State).messages }
    restoreState saved
    throw ex

elab_rules : tactic
| `(tactic| setm $pat:term $[using $usingArg]? $[$loc:location]?) =>
  withMainContext do commitIfNoExPreservingInfoAndMessages do
    let origGoal ← getMainGoal
    let (pat, { goal, holes, newMVars }) ← (replaceWithLDecls pat).run { goal := origGoal }
    goal.withContext do
      let (pat, newPatMVars) ← collectFreshMVars <| Tactic.elabTerm pat none (mayPostpone := true)
      if let some place := usingArg.map getId then
        let loc := (← getLocalDeclFromUserName place).fvarId
        defeqOrError origGoal pat (← loc.getType)
        replaceMainGoal [← goal.changeLocalDecl loc pat (checkDefEq := false)]
      else
        defeqOrError origGoal pat (← goal.getType)
        replaceMainGoal [← goal.replaceTargetDefEq pat]
      if let some loc := loc then
        -- TODO: more robust implementation with `kabstract` and `withReverted`
        -- Write as reusable API
        for fvar in holes.values do
          let some expr ← fvar.getValue? | continue
          let rewrite (loc : Option FVarId) :=
            liftMetaTactic fun goal ↦ do
              let tgt ← loc.elim goal.getType (·.getType)
              let tgt ← kabstract (← instantiateMVars tgt) (← instantiateMVars expr)
              if tgt.hasLooseBVars then
                let tgt := tgt.instantiate1 (.fvar fvar)
                if let some loc := loc then
                  return [← goal.changeLocalDecl loc tgt (checkDefEq := false)]
                else
                  return [← goal.replaceTargetDefEq tgt]
              else
                return [goal]
          withLocation (expandLocation loc) (rewrite ∘ .some) (rewrite none)
            (fun goal ↦ throwTacticEx `setm goal "Rewriting failed")
      let unassignedMVars ← (newMVars ++ newPatMVars).filterM (notM ·.isAssigned)
      if ← logUnassignedUsingErrorInfos unassignedMVars then
        throwAbortTactic

end Mathlib.Tactic.SetM
