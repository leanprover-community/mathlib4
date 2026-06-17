/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis, Kyle Miller, Gareth Ma
-/
module

public meta import Mathlib.Tactic.Set
public meta import Lean.Elab.BuiltinTerm
public meta import Batteries.Tactic.Exact

/-!
# The `setm` tactic

This module defines the `setm` tactic.
-/

meta section

open Lean Elab Tactic Meta Term Syntax

abbrev SetMReplaceM := StateT (AssocList Name MVarId) TermElabM

/-- Collect all synthetic holes and replace them with fresh metavariables. -/
partial def replaceWithMVars (stx : Term) : SetMReplaceM Term := do
  let stx ← stx.raw.replaceM fun stx ↦ do
    if let `(?$n:ident) := stx then
      let mvar ← ((← get).find? n.getId).getDM do
        let name ← mkFreshUserName n.getId
        let mvar := (← mkFreshExprMVar none (userName := name)).mvarId!
        modify (.cons n.getId mvar)
        pure mvar
      return ← withRef stx <| `(? $(mkIdent (← mvar.getTag)))
    else if let `(?_) := stx then
      let mvar ← mkFreshExprMVar none
      let name ← mkFreshUserName .anonymous
      modify (.cons name mvar.mvarId!)
      return ← withRef stx <| `(? $(mkIdent name))
    else pure none
  return ⟨stx⟩

/--
The `setm` tactic ("`set` with matching") matches a pattern containing named holes the type of a
local declaration (using the `at h` syntax) or the main goal, and introduces `let` bound variables
representing subexpressions whose location corresponds to the given named hole. These variables are
also substituted into the type of declaration (or main goal).
-/
syntax (name := setM) "setm " term (Parser.Tactic.location)? : tactic

@[tactic setM]
public def evalSetM : Tactic
  | `(tactic| setm $pat:term $[$loc:location]?) => withReducibleAndInstances do
    let locations := expandOptLocation (Lean.mkOptionalNode loc)
    withMainContext do
      let (pat, mvars) ← (replaceWithMVars pat).run {}
      let pat ← Term.elabTerm pat none
      let mut g ← getMainGoal
      for (name, mvar) in mvars.toList.reverse do
        let mvar' ← mkFreshExprMVar none
        g ← g.define name (← mvar'.mvarId!.getType) mvar'
        let (fvar, g') ← g.intro1P
        mvar.assign (.fvar fvar)
        g := g'
      replaceMainGoal [g]
      withLocation locations
        (atLocal := fun loc ↦ do
          if ← isDefEq pat (← loc.getType) then
            liftMetaTactic fun g ↦ do
              return [← g.replaceLocalDeclDefEq loc pat]
          else
            defeqError pat (← loc.getType))
        (atTarget := do
          liftMetaTactic fun g ↦ do
            if ← isDefEq pat (← g.getType) then
              return [← g.replaceTargetDefEq pat]
            else
              defeqError pat (← g.getType))
        (failed := fun _ ↦ throwError "tactic `setm` failed")
  | _ => throwUnsupportedSyntax
  where
    defeqError {α} (p e : Expr) : MetaM α :=
      throwError MessageData.ofLazyM (es := #[p, e]) do
        let (p, tgt) ← addPPExplicitToExposeDiff p e
        return m!"setm pattern{indentExpr p}\nis not definitionally equal {
          ""}to the target{indentExpr tgt}"
