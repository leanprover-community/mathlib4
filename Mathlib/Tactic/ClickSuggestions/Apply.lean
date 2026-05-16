/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState

/-!
# Support for `apply` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

structure ApplyLemma where
  name : Premise

structure ApplyKey where
  numGoals : Nat
  nameLength : Nat
  replacementSize : Nat
  name : String
  newGoals : Array AbstractMVarsResult
deriving Inhabited

instance : Ord ApplyKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def ApplyKey.isDuplicate (a b : ApplyKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
private def tacticSyntax (lemmaName : Premise) (proof : Expr) (closesGoal justLemmaName : Bool) :
    MetaM (TSyntax `tactic) := do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure closesGoal <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if closesGoal then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)
where
  hasOnlyImplicitArgs (e : Expr) : MetaM Bool := do
    let info ← getFunInfoNArgs e.getAppFn e.getAppNumArgs
    return !info.paramInfo.any (·.binderInfo.isExplicit)

/-- Generate a suggestion for applying `lem`. -/
def ApplyLemma.try (lem : ApplyLemma) : clickSuggestionsM (Result ApplyKey) :=
  withReducible do withNewMCtxDepth do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      if ← isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        newGoals := newGoals.push (← instantiateMVars (← inferType mvar))

  let makesNewMVars := newGoals.any fun goal =>
    (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof
    (closesGoal := newGoals.isEmpty) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if htmls.isEmpty then
    htmls := #[.text "Goal accomplished! 🎉️"]
  let filtered ←
    if !makesNewMVars then
      some <$> mkSuggestion tactic (.element "div" #[] htmls) htmls.isEmpty
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) htmls.isEmpty
  let pattern ← forallTelescope (← lem.name.getType) fun _ e => exprToHtml e
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
