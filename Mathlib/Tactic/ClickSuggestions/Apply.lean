/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public meta import Mathlib.Tactic.ClickSuggestions.Util

import all Lean.Meta.Tactic.Apply

/-!
# Support for `apply` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/-- The structure for `apply` lemmas stored in the `RefinedDiscrTree`. -/
structure ApplyLemma where
  /-- The lemma -/
  name : Premise

/-- The key that is used for sorting and deduplicating `apply` lemmas. -/
structure ApplyKey where
  /-- How many new goals are generated. -/
  numGoals : Nat
  /-- The name length of the used lemma. -/
  nameLength : Nat
  /-- The total length of the new goals when printed. -/
  replacementSize : Nat
  /-- The name of the used lemma. -/
  name : String
  /-- The new goals. -/
  newGoals : Array AbstractMVarsResult
deriving Inhabited

instance : Ord ApplyKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

/-- Whether the two suggestions are duplicates of each other. -/
def ApplyKey.isDuplicate (a b : ApplyKey) : MetaM Bool :=
  pure (a.newGoals.size == b.newGoals.size) <&&>
  a.newGoals.size.allM fun i _ =>
    pure (a.newGoals[i]!.mvars.size == b.newGoals[i]!.mvars.size)
      <&&> isExplicitEq a.newGoals[i]!.expr b.newGoals[i]!.expr

/-- Return the `apply` tactic that performs the application. -/
private def tacticSyntax (lemmaName : Premise) (proof : Expr) (isClosing justLemmaName : Bool) :
    MetaM (TSyntax `tactic) := do
  if justLemmaName then
    let id := mkIdent (← lemmaName.unresolveName)
    -- We can only use `exact` instead of `apply` if the proof has no explicit arguments.
    if ← pure isClosing <&&> hasOnlyImplicitArgs proof then
      `(tactic| exact $id)
    else
      `(tactic| apply $id)
  else
    let proof ← withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
    if isClosing then
      `(tactic| exact $proof)
    else
      `(tactic| refine $proof)
where
  hasOnlyImplicitArgs (e : Expr) : MetaM Bool := do
    let info ← getFunInfoNArgs e.getAppFn e.getAppNumArgs
    return !info.paramInfo.any (·.binderInfo.isExplicit)

/-- Generate the suggestion for applying `lem`. -/
def ApplyLemma.try (lem : ApplyLemma) (assignableMVars : Array Expr) :
    ClickSuggestionsM (Result ApplyKey) := do
  let (proof, mvars, binderInfos, e) ← lem.name.forallMetaTelescopeReducing
  let target ← (← read).goal.getType
  unless ← isDefEq e target do throwError "{e} does not unify with {target}"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mvars ← mvars.filterM (not <$> ·.mvarId!.isAssigned)
  -- Reorder the goals as `apply` would.
  let mvars ← reorderGoals mvars .nonDependentFirst
  let mut newGoals := #[]
  let mut justLemmaName := true
  for mvarId in mvars do
    let type ← instantiateMVars <| ← mvarId.getType
    if ← isProp type then
      if let some fvarId ← withNewMCtxDepth <| findLocalDeclWithType? type then
        mvarId.assign (.fvar fvarId)
        justLemmaName := false
        continue
    newGoals := newGoals.push type
  let isClosing := newGoals.isEmpty
  let unhelpfulMVars ← hasUnhelpfulMVars mvars.toArray assignableMVars newGoals
  let proof ← instantiateMVars proof
  let key := {
    numGoals := newGoals.size
    nameLength := lem.name.length
    replacementSize := ← newGoals.foldlM (init := 0) fun s g =>
      return (← ppExpr g).pretty.length + s
    name := lem.name.toString
    newGoals := ← newGoals.mapM (abstractMVars ·)
  }
  let tactic ← tacticSyntax lem.name proof (isClosing := isClosing) (justLemmaName := justLemmaName)
  let mut htmls := #[]
  for goal in newGoals do
    htmls := htmls.push <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  if isClosing then
    htmls := #[.text "Goal accomplished! 🎉️"]
    addSolvedSuggestion tactic
  let filtered ←
    if unhelpfulMVars then
      pure none
    else
      some <$> mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls) (isClosing := isClosing)
  let pattern ← do
    let (_, _, e) ← forallMetaTelescopeReducing (← lem.name.getType)
    exprToHtml e
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
