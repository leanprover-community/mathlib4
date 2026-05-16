/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public import Mathlib.Tactic.ApplyAt

/-!
# Support for `apply at` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

structure ApplyAtLemma where
  name : Premise

structure ApplyAtKey where
  numGoals : Nat
  nameLength : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

instance : Ord ApplyAtKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def ApplyAtKey.isDuplicate (a b : ApplyAtKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
private def tacticSyntax (lem : ApplyAtLemma) : clickSuggestionsM (TSyntax `tactic) := do
  -- let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab app.proof)
  `(tactic| apply $(mkIdent (← lem.name.unresolveName)) at $(← getHypIdent!))

/-- Generate a suggestion for applying `lem`. -/
def ApplyAtLemma.try (lem : ApplyAtLemma) : clickSuggestionsM (Result ApplyAtKey) :=
  withReducible do withNewMCtxDepth do
  let (_proof, mvars, binderInfos, replacement) ← lem.name.forallMetaTelescopeReducing
  let mvar := mvars.back!
  let mvars := mvars.pop
  let fvarId := (← read).hyp?.get!
  unless ← isDefEq mvar (.fvar fvarId) do
    throwError "{← inferType mvar} does not unify with {← fvarId.getType}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      newGoals := newGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars replacement
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    newGoals.any fun goal ↦ (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := (← newGoals.mapM (abstractMVars ·)).push (← abstractMVars replacement)
  }
  let tactic ← tacticSyntax lem
  let mut htmls := #[← exprToHtml replacement]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if makesNewMVars then
      pure none
    else
      some <$> mkSuggestion tactic (.element "div" #[] htmls)
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← lem.name.getType) fun xs _ => do
    exprToHtml (← inferType xs.back!)
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
