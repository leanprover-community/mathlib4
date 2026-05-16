/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.ClickSuggestions.SectionState
public import Mathlib.Order.Antisymmetrization

/-!
# Support for `grw` suggestions in `#click_suggestions`
-/

public meta section

namespace Mathlib.Tactic.ClickSuggestions

open Lean Meta Mathlib.Tactic ProofWidgets Jsx

/-- `GRewritePos` contains the ìnformation about a given subexpression position needed for
applying a  `grw` lemma. -/
structure GrwPos where
  /-- The name of the relation. -/
  relName : Name
  /-- The expression of the relation. -/
  relation : Expr
  /-- `symm` is `none` if the given relations are symmetric.
  `symm` is `true` when you can only rewrite from right to left. -/
  symm? : Option Bool

/-- Given the relation that we can use to rewrite at the give position, figure out all of the
subrelations that could be used instead. -/
private def gcongrBackward (relName : Name) (relation : Expr) (symm : Bool) :
    MetaM (Array GrwPos) := do
  let type ← inferType relation
  let α ← mkFreshTypeMVar
  unless ← isDefEq type (.forallE `_ α (.forallE `_ α (.sort 0) .default) .default) do
    throwError "invalid relation {relation}"
  let α ← instantiateMVars α
  let u ← getDecLevel α
  withLocalDeclD `a α fun a ↦ do
  withLocalDeclD `b α fun b ↦ do
  withNewMCtxDepth do
  -- Any relation `r` can be proved from `AntisymmRel r`, so we add this as a possible relation
  let antiSymm := mkApp2 (.const ``AntisymmRel [u]) α relation
  let mut result : Array GrwPos :=
    #[{ relName := ``AntisymmRel, relation := antiSymm, symm? := none }]
  -- If `relName` is symmetric, then include the reverse as a possible relation (`symm? := none`)
  let symm? ← try
    let dummyVar ← mkFreshExprMVar (mkApp2 relation a b)
    if let mkApp2 relation' b' a' ← inferType (← dummyVar.applySymm) then
      if relation' == relation && b == b' && a == a' then
        pure none
      else
        pure symm
    else
      pure symm
    catch _ => pure symm
  result := result.push { relName, relation, symm? }
  -- For `≤` and `⊆` we add `<` and `⊂` respectively as possible relations.
  match relName with
  | ``LE.le =>
    if let some pos ← tryApply ``le_of_lt ``LT.lt then
      result := result.push pos
  | ``HasSubset.Subset =>
    if let some pos ← tryApply ``subset_of_ssubset ``HasSSubset.SSubset then
      result := result.push pos
  | _ => pure ()
  return result
where
  tryApply (appName relName : Name) : MetaM (Option GrwPos) := do
    let (mvars, bi, rel) ← forallMetaTelescope (← inferType (← mkConstWithFreshMVarLevels appName))
    try
      if ← isDefEq rel.appFn!.appFn! relation then
        synthAppInstances default default mvars bi false false
        let rel ← instantiateMVars (← inferType mvars.back!).appFn!.appFn!
        return some { relName, relation := rel, symm? := symm }
      return none
    catch _ =>
      return none

/-- This function is passed to `MVarId.gcongr` as the main discharger.
It doesn't try to prove the goal, but instead observes what the goal is,
to help determine which lemmas could work with `grw`. -/
private def dummyDischarger (ref : IO.Ref (Array GrwPos)) (hyp? : Bool) (fvar : Expr)
    (goal : MVarId) : MetaM Bool := do
  let relation ← instantiateMVars (← goal.getType)
  let e@(mkApp2 relation lhs rhs) := relation | throw <| .error default "dummyError"
  let .const relName _ := relation.getAppFn | throw <| .error default "dummyError"
  if relName matches ``Eq | ``Iff then throw <| .error default "dummyError"
  let symm ←
    if lhs.cleanupAnnotations == fvar then
      pure hyp?
    else if rhs.cleanupAnnotations == fvar then
      pure !hyp?
    else
      throwError "{e} doesn't have {fvar} on either side"
  ref.set (← gcongrBackward relName relation symm)
  throw <| .error default "dummyError"

/-- Determine possible ways in which a `grw` call could rewrite at the given subexpression. -/
def getGrwPos? (rootExpr subExpr : Expr) (pos : SubExpr.Pos) (hyp? : Bool) :
    MetaM (Array GrwPos) := do
  withLocalDeclD `_a (← inferType subExpr) fun fvar => do
  let root' ← replaceSubexpr (fun _ => pure (GCongr.mkHoleAnnotation fvar)) pos rootExpr
  let imp := Expr.forallE `_a rootExpr root' .default
  let dummyGoal ← mkFreshExprMVar imp
  let ref ← IO.mkRef #[]
  try
    _ ← dummyGoal.mvarId!.gcongr false |>.run (mainGoalDischarger := dummyDischarger ref hyp? fvar)
  catch ex =>
    if (← ex.toMessageData.toString) != "dummyError" then
      return #[]
  let result ← ref.get
  /- I am not entirely sure if this can come up in practice, but we check that the relation
  that was found doesn't contain any free variables that are now out of scope. -/
  for { relation, .. } in result do
    unless (collectFVars {} relation).fvarIds.all (← getLCtx).contains do
      return #[]
  return result


/-- The structure for rewrite lemmas stored in the `RefinedDiscrTree`. -/
structure GrwLemma where
  /-- The lemma -/
  name : Premise
  /-- `symm` is `true` when rewriting from right to left -/
  symm : Bool
  /-- `relName` is the relation of the lemma. -/
  relName : Name

structure GrwInfo where
  rootExpr : Expr
  subExpr : Expr
  rwKind : RwKind
  gpos : Array GrwPos

structure GrwKey where
  numGoals : Nat
  nameLength : Nat
  replacementSize : Nat
  name : String
  -- TODO: in this implementation, we conclude that two rewrites are the same if they
  -- rewrite into the same expression. But there can be two rewrites that have
  -- different side conditions!
  replacement : AbstractMVarsResult
deriving Inhabited

instance : Ord GrwKey where
  compare a b :=
    (compare a.1 b.1).then <|
    (compare a.2 b.2).then <|
    (compare a.3 b.3).then <|
    (compare a.4 b.4)

def GrwKey.isDuplicate (a b : GrwKey) : MetaM Bool :=
  pure (a.replacement.mvars.size == b.replacement.mvars.size)
    <&&> isExplicitEq a.replacement.expr b.replacement.expr

/-- Return the rewrite tactic that performs the rewrite. -/
private def tacticSyntax (lem : GrwLemma) (i : GrwInfo) (proof : Expr) (justLemmaName : Bool) :
    clickSuggestionsM (TSyntax `tactic) := do
  let proof ← if justLemmaName then
      `(term| $(mkIdent <| ← lem.name.unresolveName))
    else
      withOptions (pp.mvars.set · false) (PrettyPrinter.delab proof)
  mkRewrite i.rwKind lem.symm proof (← getHypIdent?) (grw := true)

/-- Generate the suggestion for rewriting with `lem`. -/
def GrwLemma.try (i : GrwInfo) (lem : GrwLemma) : clickSuggestionsM (Result GrwKey) := do
  withReducible do withNewMCtxDepth do
  let mctx ← getMCtx
  (·.getDM do throwError "no suitable `grw` relation was found") =<< i.gpos.findSomeM? fun pos ↦ do
  unless lem.relName == pos.relName && pos.symm?.all (· == lem.symm) do return none
  let (proof, mvars, binderInfos, rel) ← lem.name.forallMetaTelescopeReducing
  let mkApp2 rel lhs rhs := rel.cleanupAnnotations | return none
  unless ← isDefEq rel pos.relation do setMCtx mctx; return none
  some <$> do
  let e := i.subExpr
  let (lhs, rhs) := if lem.symm then (rhs, lhs) else (lhs, rhs)
  let lhsOrig := lhs; let mctxOrig ← getMCtx
  unless ← isDefEq e lhs do
    throwError "{lhs} does not unify with {e}"
  -- just like in `kabstract`, we compare the `HeadIndex` and number of arguments
  let lhs ← instantiateMVars lhs
  if lhs.toHeadIndex != e.toHeadIndex || lhs.headNumArgs != e.headNumArgs then
    throwError "{lhs} and {e} do not match according to the head-constant indexing"
  synthAppInstances `click_suggestions default mvars binderInfos false false
  let mut extraGoals := #[]
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      extraGoals := extraGoals.push (← instantiateMVars (← inferType mvar))

  let replacement ← instantiateMVars rhs
  let makesNewMVars :=
    (replacement.findMVar? (mvars.contains <| .mvar ·)).isSome ||
    extraGoals.any fun goal ↦ (goal.findMVar? (mvars.contains <| .mvar ·)).isSome
  let proof ← instantiateMVars proof
  let isRefl ← isExplicitEq e replacement
  let justLemmaName ←
    if i.rwKind matches .hasBVars then pure true
    else withMCtx mctxOrig do kabstractFindsPositions i.rootExpr lhsOrig (← read).pos
  let key := {
    numGoals := extraGoals.size
    nameLength := lem.name.length
    replacementSize := (← ppExpr replacement).pretty.length
    name := lem.name.toString
    replacement := ← abstractMVars replacement
  }
  let tactic ← tacticSyntax lem i proof justLemmaName
  let mut htmls := #[← exprToHtml replacement]
  for goal in extraGoals do
    -- TODO: think more carefully about which goals should be displayed
    -- Are there lemmas where a hypothesis is marked as implicit,
    -- which we would still want to show as a new goal?
    htmls := htmls.push
      <div> <strong className="goal-vdash">⊢ </strong> {← exprToHtml goal} </div>
  let filtered ←
    if !isRefl && !makesNewMVars then
      some <$> mkSuggestion tactic (.element "div" #[] htmls)
    else
      pure none
  htmls := htmls.push <div> {← lem.name.toHtml} </div>
  let unfiltered ← mkSuggestion tactic (.element "div" #[] htmls)
  let pattern ← forallTelescopeReducing (← lem.name.getType) fun _ e => do
    let mkApp2 _ lhs rhs := (← instantiateMVars e).cleanupAnnotations
      | throwError "Expected relation, not {indentExpr e}"
    exprToHtml <| if lem.symm then rhs else lhs
  return { filtered, unfiltered, key, pattern }

end Mathlib.Tactic.ClickSuggestions
