/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Kyle Miller, Gareth Ma
-/
module

public meta import Mathlib.Tactic.Core

/-!
# The `setm` tactic

This module defines the `setm` tactic.
-/

meta section

open Lean Mathlib Elab Tactic Meta Term Syntax

abbrev SetMReplaceM := StateT (List (Name × MVarId)) TermElabM

/-- Collect all synthetic holes and replace them with fresh metavariables. -/
partial def replaceWithMVars (stx : Term) : SetMReplaceM Term := do
  let stx ← stx.raw.replaceM fun stx ↦ do
    let pair ←
      if let `(?$n:ident) := stx then
        (← get).find? (·.1 == n.getId) |>.getDM do
          let name ← mkFreshUserName n.getId
          let mvar ← mkFreshExprMVar none (userName := name)
          pure (n.getId, mvar.mvarId!)
      else if let `(?_) := stx then
        let name ← mkFreshUserName `x
        let mvar ← mkFreshExprMVar none (userName := name)
        pure (name, mvar.mvarId!)
      else return none
    modify (.cons pair)
    return ← withRef stx <| `(? $(mkIdent (← pair.2.getTag)))
  return ⟨stx⟩

/--
The `setm` tactic ("`set` with matching") matches a pattern containing named holes to the type of
a target the goalor a local declaration, via the `using` syntax below.


local declaration (using the `at h` syntax) or the main goal, and introduces `let` bound variables
representing subexpressions whose location corresponds to the given named hole. These variables are
also substituted into the type of declaration (or main goal).
-/
syntax (name := setM) "setm " term ("using" ident)? (Parser.Tactic.location)? : tactic

def defeqError {α} (p e : Expr) : MetaM α :=
  throwError MessageData.ofLazyM (es := #[p, e]) do
    let (p, tgt) ← addPPExplicitToExposeDiff p e
    return m!"setm pattern{indentExpr p}\nis not definitionally equal {
      ""}to the target{indentExpr tgt}"

elab_rules : tactic
| `(tactic| setm $pat:term $[using $usingArg]? $[$loc:location]?) =>
  withMainContext do
    let (pat, mvars) ← (replaceWithMVars pat).run {}
    let pat ← Term.elabTerm pat none
    let mut g ← getMainGoal
    for (name, mvar) in mvars.reverse do
      let mvar' ← mkFreshExprMVar none
      g ← g.define name (← mvar'.mvarId!.getType) mvar'
      let (fvar, g') ← g.intro1P
      mvar.assign (.fvar fvar)
      g := g'
    replaceMainGoal [g]
    withMainContext <| withReducibleAndInstances do
      if let some place := usingArg.map getId then
        let loc := (← getLocalDeclFromUserName place).fvarId
        if ← isDefEq pat (← loc.getType) then
          replaceMainGoal [← g.changeLocalDecl loc pat false]
        else
          defeqError pat (← loc.getType)
      else
        if ← isDefEq pat (← g.getType) then
          replaceMainGoal [← g.replaceTargetDefEq pat]
        else
          defeqError pat (← g.getType)
      if let some loc := loc then
        for (name, _) in mvars do
        let expr := (← getLocalDeclFromUserName name).value
        evalTactic (← `(tactic| try
          rewrite [show $(← Term.exprToSyntax expr) = $(mkIdent name) from rfl] $loc))
