/-
Copyright (c) 2026 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public meta import Mathlib.Tactic.Core
public meta import Lean.Elab.Tactic.Rewrite
public meta import Mathlib.Lean.Elab.Tactic.Basic

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

/-- Check that `p` and `e` are reducibly definitionally equal in the context of goal `goal`, or
throw a nicely-formatted error.
-/
def defeqOrError (goal : MVarId) (p e : Expr) : MetaM Unit :=
  -- We use `withAssinableSyntheticOpaque` here as elaboration of the pattern can create
  -- metavariables of `.syntheticOpaque` kind that could be assigned by the `isDefEq`. See the
  -- test file for a concrete example.
  --
  -- TODO: `withoutProofIrrelevance` is not doing what we would expect it to do because of what
  -- seems like a bug in Lean, see the withoutProofIrrelevance section in the test file and
  -- the issue mentioned there.
  unless ← withReducible <| withoutProofIrrelevance <| withAssignableSyntheticOpaque
      <| isDefEq p e do
    throwTacticEx `setm goal <| MessageData.ofLazyM (es := #[p, e]) do
      let (p, tgt) ← addPPExplicitToExposeDiff p e
      return m!"Pattern{indentExpr p}\nis not definitionally equal \
        to the target{indentExpr tgt}"

/-- `setm patt` matches `patt`, a term containing named holes (like `?a`) to the goal, and creates
named local declarations for the matched holes with their assigned expressions as values. Moreover,
it will replace the matches with their new names. This tactic can be used to give a name to a
complicated subexpression appearing in the goal or a hypothesis.

* `setm patt using h` matches `patt` with the local hypothesis named `h` instead of the main goal.
* `setm patt at loc` also rewrites by the newly-introduced local declarations at the location(s)
  `loc`.

Examples:
```lean
example : ∃ n, n = 2 ^ 10 - 1 := by
  setm ∃ _, _ = ?a
  /-
  a := 2 ^ 10 - 1
  ⊢ ∃ n, n = a
  -/
  exact .intro a rfl
```

`using h` matches against `h` instead of the goal:
```lean
example (h : 1 + 2 = 3) : ∃ n, n = 2 := by
  setm _ + ?a = _ using h
  /-
  a := 2
  h : 1 + a = 3
  ⊢ ∃ n, n = 2
  -/
  exact .intro a rfl
```

`at h₂` rewrites `h₂` so that it uses `a`:
```lean
example (h₁ : 1 + 2 = 3) (h₂ : 2 + 2 = 4) : ∃ n, n = 2 := by
  setm _ + ?a = _ using h₁ at h₂
  /-
  a : Nat := 2
  h₁ : 1 + a = 3
  h₂ : a + a = 4
  ⊢ ∃ n, n = 2
  -/
  exact .intro a rfl
```
-/
syntax (name := setM) "setm " term (" using " ident)? (Parser.Tactic.location)? : tactic

elab_rules : tactic
| `(tactic| setm $origPat:term $[using $usingArg]? $[$loc:location]?) =>
  /- We don't use `withNewMCtxDepth` because it also resets the whole metavariable context and this
  tactic creates new metavariables. -/
  withMainContext <| commitIfNoExPreservingInfoAndMessages do
    let origGoal ← getMainGoal
    let (pat, { goal, holes, newMVars }) ← (replaceWithLDecls origPat).run { goal := origGoal }
    goal.withContext do
      let (pat, newPatMVars) ← collectFreshMVars <| Tactic.elabTerm pat none (mayPostpone := true)
      if let some usingArg := usingArg then
        withRef (mkNullNode #[origPat, usingArg]) do
          let loc := (← getLocalDeclFromUserName usingArg.getId).fvarId
          defeqOrError origGoal pat (← loc.getType)
          replaceMainGoal [← goal.changeLocalDecl loc pat (checkDefEq := false)]
      else
        withRef origPat do
          defeqOrError origGoal pat (← goal.getType)
          replaceMainGoal [← goal.replaceTargetDefEq pat]
      if let some loc := loc then
        for fvar in holes.values do
          let some expr ← fvar.getValue? | continue
          let rewrite (loc : Option FVarId) :=
            -- TODO: this kabstract rewriting could possibly be made into a reusable API
            liftMetaTactic fun goal ↦ do
              let tgt ← loc.elim goal.getType (·.getType)
              let tgt ← withReducible (kabstract (← instantiateMVars tgt) (← instantiateMVars expr))
              if tgt.hasLooseBVars then
                let tgt := tgt.instantiate1 (.fvar fvar)
                if let some loc := loc then
                  return [← goal.changeLocalDecl loc tgt (checkDefEq := false)]
                else
                  return [← goal.replaceTargetDefEq tgt]
              else
                return [goal]
          withRef loc <| withLocation (expandLocation loc) (rewrite ∘ some) (rewrite none)
            (fun goal ↦ throwTacticEx `setm goal "Rewriting failed")
      let unassignedMVars ← (newMVars ++ newPatMVars).filterM (notM ·.isAssigned)
      logUnassignedAndAbort unassignedMVars
      if newMVars.isEmpty then
        logWarningAt origPat m!"No holes (`?n`, `?_`) were present in the `setm` pattern. \
          This means `setm` has no effect."

end Mathlib.Tactic.SetM
