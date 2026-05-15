/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState

/-!
# Support for `rw` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta ProofWidgets Jsx

/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure RwLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool

structure RwInfo where
  rootExpr : Expr
  subExpr : Expr
  /-- Recall that we also suggest rewrites for subexpressions of the selected expression,
  in order to be able to rewrite with partially applied lemmas. -/
  pos : SubExpr.Pos
  rwKind : RwKind

structure RwKey where
  numGoals : Nat
  symm : Bool
  nameLenght : Nat
  replacementSize : Nat
  name : String
  -- TODO: in this implementation, we conclude that two rewrites are the same if they
  -- rewrite into the same expression. But there can be two rewrites that have
  -- different side conditions!
  replacement : AbstractMVarsResult
deriving Inhabited

instance : Ord RwKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4).then <|
    (compare a.5 b.5)

def RwKey.isDuplicate (a b : RwKey) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

/-- Return the rewrite tactic that performs the rewrite. -/
private def tacticSyntax (lem : RwLemma) (rwKind : RwKind) (hyp? : Option Ident) (proof : Expr)
    (justLemmaName : Bool) : MetaM (TSyntax `tactic) := do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite rwKind lem.symm proof hyp?

def RwLemma.try (i : RwInfo) (lem : RwLemma) : clickSuggestionsM (Result RwKey) :=
  withReducible do withNewMCtxDepth do
  let e := i.subExpr
  let (proof, mvars, binderInfos, eqn) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 _ lhs rhs ← whnf eqn | throwError "Exected an equality or iff, not {eqn}"
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  unless ← isDefEq lhs e do throwError "{lhs} does not unify with {e}"
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  -- TODO: if the `headIndex` doesn't match, then use `simp_rw` instead of `rw` in the suggestion,
  -- instead of just not showing the suggestion.
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    throwError "{lhs} and {e} do not match according to the head-constant indexing"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut extraGoals := #[]
  let mut justLemmaName := true
  let mut rwKind := i.rwKind
  for mvar in mvars, bi in binderInfos do
    unless ← mvar.mvarId!.isAssigned do
      if ← pure (rwKind matches .valid ..) <&&> isProof mvar <&&> mvar.mvarId!.assumptionCore then
        justLemmaName := false
      else
        extraGoals := extraGoals.push (← instantiateMVars (← inferType mvar), bi)

  let replacement ← instantiateMVars rhs
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    extraGoals.any fun goal ↦ (goal.1.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  if let .valid tpCorrect _ := rwKind then
    if justLemmaName then
      if ← withMCtx mctxOrig do kabstractFindsPositions i.rootExpr lhsOrig i.pos then
        rwKind := .valid tpCorrect none
      else
        justLemmaName := false
  let key := {
    numGoals := extraGoals.size
    symm := lem.symm
    nameLenght := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  let tactic ← tacticSyntax lem rwKind (← getHypIdent?) proof justLemmaName
  let mut htmls := #[← exprToHtml replacement]
  for (mvarId, bi) in extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    if bi.isExplicit then
      htmls := htmls.push
        <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml mvarId} </div>
  let filtered ←
    if !isRefl && !makesNewMVars then
      some <$> mkSuggestion tactic (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push (<div> {← lem.name.toHtml} </div>)
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← lem.name.getType) fun _ e => do
    let mkApp2 _ lhs rhs ← whnf e | throwError "Expected equation, not{indentExpr e}"
    exprToHtml <| if lem.symm then rhs else lhs
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
