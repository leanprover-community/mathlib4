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
target is the goal, but it can be selected to be a local declaration via the `using` syntax.
Optionally, with the syntax `at loc`, it also rewrites at locations `loc` to replace the occurrences
of the matched expressions with the newly-introduced local declarations.


## Todo

It would be nice if the tactic was be made to work for non-constants under binders (by adding forall
binders to the local declarations).

-/

meta section

open Lean Mathlib Elab Tactic Meta Term Syntax

structure SetMReplaceState where
  goal : MVarId
  /-- Created names and their fvars, in the order they appear in the pattern. -/
  holes : Array (Name × FVarId)

abbrev SetMReplaceM := StateT SetMReplaceState TermElabM

/-- Traverse all synthetic holes, creating local declarations for them. -/
def replaceWithLDecls (stx : Syntax) : SetMReplaceM Syntax :=
  stx.replaceM fun stx ↦ do
    let (name, _) ←
      if let `(?$n:ident) := stx then
        let name := n.getId
        (← get).holes.find? (·.fst == name) |>.getDM do
          createLDecl name
      else if let `(?_) := stx then
        let name ← mkFreshUserName `x
        createLDecl name
      else
        -- Not a synthetic hole.
        return none
    return ← withRef stx <| `($(mkIdent name))
  where
    createLDecl name : SetMReplaceM (Name × FVarId) := do
      let mvar ← mkFreshExprMVar none
      let goal ← (← get).goal.define name (← mvar.mvarId!.getType) mvar
      let (fvar, goal) ← goal.intro1P
      modify fun s ↦ {s with goal, holes := s.holes.push (name, fvar)}
      return (name, fvar)

/--
* `setm expr`, where `expr` is a term containing named holes (like `?a`) will match `expr` to the
  current goal and create local declarations assigning the hole names to their inferred value.
  Moreover, it will replace the matches with their new names.
* `setm expr using h` is like `setm expr`, except that `expr` is matched with the local hypothesis
  `h` instead.
* `setm expr [using h] at loc` is like the above, except that it also rewrites the newly-introduced
  local declarations at the locations `loc`.
-/
syntax (name := setM) "setm " term ("using" ident)? (Parser.Tactic.location)? : tactic

def defeqOrError (p e : Expr) : TermElabM Unit :=
  unless (← isDefEq p e) do
    throwError MessageData.ofLazyM (es := #[p, e]) do
      let (p, tgt) ← addPPExplicitToExposeDiff p e
      return m!"setm pattern{indentExpr p}\nis not definitionally equal {
        ""}to the target{indentExpr tgt}"

elab_rules : tactic
| `(tactic| setm $pat:term $[using $usingArg]? $[$loc:location]?) =>
  withMainContext do
    let goal ← getMainGoal
    let (pat, {goal, holes}) ← (replaceWithLDecls pat).run {goal, holes := {}}
    goal.withContext <| withReducibleAndInstances do
      let pat ← Term.elabTerm pat none
      if let some place := usingArg.map getId then
        let loc := (← getLocalDeclFromUserName place).fvarId
        defeqOrError pat (← loc.getType)
        replaceMainGoal [← goal.changeLocalDecl loc pat false]
      else
        defeqOrError pat (← goal.getType)
        replaceMainGoal [← goal.replaceTargetDefEq pat]
      if let some loc := loc then
        for (name, fvar) in holes do
          let some expr ← fvar.getValue? | continue
          let eq ← `(show $(← Term.exprToSyntax expr) = $(mkIdent name) from rfl)
          withLocation (expandLocation loc)
            (discard <| tryTactic <| rewriteLocalDecl eq false ·)
            (discard <| tryTactic <| rewriteTarget eq false)
            (fun _ ↦ throwError "setm rewrite failed")
