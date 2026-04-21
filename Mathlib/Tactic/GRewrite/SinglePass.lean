/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GRewrite.Elab

/-!
# The generalized rewriting tactic 2.0
-/

public meta section


namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

initialize registerTraceClass `Meta.grewrite
initialize registerTraceClass `Meta.grewrite.gcongr (inherited := true)

structure GRewriteLemma where
  symm : Bool
  levelParams : Array Name := #[]
  proof : Expr
  headIdx : HeadIndex
  headNumArgs : Nat
  relName : Name

abbrev GRewriteM := ReaderT GRewriteLemma StateRefT (Std.HashSet Expr) GCongr.GCongrM

def GRewriteLemma.getValue (lem : GRewriteLemma) : MetaM Expr := do
  let us ← lem.levelParams.mapM fun _ => mkFreshLevelMVar
  return lem.proof.instantiateLevelParamsArray lem.levelParams us

def GRewriteLemma.apply (g : MVarId) (lem : GRewriteLemma) (config : GRewrite.Config) :
    GRewriteM Unit := do
  let proof ← lem.getValue
  let (mvars, _, rel) ← forallMetaTelescopeReducing (← inferType proof)
  guard <| ← withConfig (fun oldConfig => { config, oldConfig with }) <|
    isDefEq (← g.getType) rel
  for mvar in mvars do
    unless ← mvar.mvarId!.isAssigned do
      let type ← mvar.mvarId!.getType
      if (← isClass? type).isSome then
        if let some inst ← synthInstance? type then
          guard <| ← isDefEq mvar inst
          continue
    pushNewGoal mvar.mvarId!
  g.assign (mkAppN proof mvars)

mutual

private partial def processGCongrLemma (g : MVarId) (lem : GCongrLemma) (inv : Bool)
    (config : GRewrite.Config) :
    GRewriteM Bool := do
  let (mainGoals, sideGoals) ←
    try applyGCongrLemma g lem catch _ => return false
  /- Synthesize instances. Allow Synthesis to get stuck, because e.g. with
  `{hs : s.Finite} {ht : t.Finite} : s ⊆ t → hs.toFinset ⊆ ht.toFinset`,
  either `s` or `t` is still a metavariable at this point. -/
  let mut unsolvedSideGoals := #[]
  for mvarId in sideGoals do
    let type ← mvarId.getType
    if (← isClass? type).isSome then
      match ← trySynthInstance type with
      | .some inst => mvarId.assign inst; continue
      | .none => return false
      | .undef => pure ()
    unsolvedSideGoals := unsolvedSideGoals.push mvarId
  -- Then, recursively rewrite in the main subgoals
  trace[Meta.grewrite.gcongr] "applied lemma {.ofConstName lem.declName}"
  let mut anyProgress := false
  for (g, isContra) in mainGoals do
    if ← grewriteCongr g (inv != isContra) config then
      anyProgress := true
    else
      try g.applyRfl catch _ => return false
  -- Only continue if at least one rewrite happened
  unless anyProgress do return false
  -- Finally, close all remaining side goals
  for mvarId in unsolvedSideGoals do
    let type ← mvarId.getType
    if (← isClass? type).isSome then
      let some inst ← synthInstance? type | return false
      mvarId.assign inst
    else
      dischargeSide mvarId
  return true

private partial def grewriteCongr (g : MVarId) (inv : Bool)
    (config : GRewrite.Config) : GRewriteM Bool := g.withContext do
  let rel ← g.getType'
  withTraceNodeBefore `Meta.grewrite (fun _ ↦ return m!"rewriting {rel}") do
  let some (relName, lhs, rhs) := getRel rel |
    throwTacticEx `grewrite g m!"{rel} is not a relation"
  let cacheKey := updateRel rel (.fvar ⟨`grewrite.placeholder⟩) inv
  if (← get).contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return false
  let e := if inv then rhs else lhs
  let eWhnf ← whnf e
  -- Try to use the grewrite lemma.
  let lem ← read
  if relName == lem.relName && eWhnf.toHeadIndex == lem.headIdx &&
      eWhnf.headNumArgs == lem.headNumArgs then
    let mctx ← getMCtx
    try
      let g ← if inv == lem.symm then pure g else g.applySymm
      lem.apply g config
      trace[Meta.grewrite] "applied rewrite lemma `{lem.proof}` to{indentExpr (← g.getType)}"
      return true
    catch _ =>
      setMCtx mctx
  if let some (head, args) := getCongrAppFnArgs e then
    let key := { relName, head, arity := args.size }
    let mut lemmas := (gcongrExt.getState (← getEnv)).getD key []
    if relName == `_Implies then
      lemmas := lemmas ++ relImpRelLemma args.size
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if ← processGCongrLemma g gcongrLem inv config then
        return true
      else
        setMCtx mctx
  modify (·.insert cacheKey)
  return false

end

def _root_.Lean.MVarId.grewriteImp (goal : MVarId) (e : Expr) (lem : GRewriteLemma)
    (forwardImp : Bool) (config : GRewrite.Config) : MetaM GRewriteResult :=
  withReducible do goal.withContext do
    goal.checkNotAssigned `grewrite
    let eNew ← mkFreshExprMVar (Expr.sort 0)
    let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
    let imp := if forwardImp then mkImp e eNew else mkImp eNew e
    let congrGoal ← mkFreshExprMVar imp
    let (progress, newGoals) ←
      grewriteCongr congrGoal.mvarId! (!forwardImp) config |>.run lem |>.run' {} |>.run
    if progress then
      let eNew ← instantiateMVars eNew
      return { eNew, impProof := congrGoal, mvarIds := newGoals.toList }
    else
      let (_, _, rel) ← forallMetaTelescopeReducing (← inferType (← lem.getValue))
      let some (_, lhs, rhs) := getRel (← whnf rel) | unreachable!
      let pattern := if lem.symm then rhs else lhs
      throwTacticEx `grewrite goal
        m!"Did not find a suitable occurrence of {indentExpr pattern}\n\
        in the target expression{indentExpr e}"

open Lean Meta Elab Parser

private def elabGRewriteLemma (stx : Syntax) (symm : Bool) :
    TermElabM GRewriteLemma := do
  Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  let e ← instantiateMVars e
  if e.hasSyntheticSorry then
    throwAbortTactic
  withReducible do
  let (mvars, _, rel) ← forallMetaTelescopeReducing (← inferType e)
  let backward := rel.getAppFn'.constName?.any
    (· matches ``GE.ge | ``GT.gt | ``Superset | ``SSuperset)
  let symm := symm != backward
  let some (relName, lhs, rhs) := getRel (← whnf rel) |
    let valueDescr := if (← Meta.isProp rel) then "a proof of" else "a value of type"
    throwError m!"Invalid grewrite argument: Expected a relation or definition name, \
      but{inlineExpr (mkAppN e mvars)}is {valueDescr}{indentExpr rel}"
  let (headIdx, headNumArgs) :=
    if symm then (rhs.toHeadIndex, rhs.headNumArgs) else (lhs.toHeadIndex, lhs.headNumArgs)
  if headIdx matches .mvar _ then
    throwError "Invalid grewrite argument: The pattern to be substituted \
      is a metavariable (`{lhs}`) in this relation{indentExpr rel}"
  let (levelParams, proof) ←
    if e.hasMVar then
      let r ← abstractMVars e
      pure (r.paramNames, r.expr.eta)
    else
      pure (#[], e)
  return { symm, levelParams, proof, headIdx, headNumArgs, relName }

private def elabGRewrite (mvarId : MVarId) (e : Expr) (stx : Syntax) (forwardImp symm : Bool)
    (config : GRewrite.Config) : TermElabM GRewriteResult := do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let lem ← elabGRewriteLemma stx (symm := symm)
  -- TODO: decide whether to prove `→` or `↔`.
  if lem.relName matches ``Eq | ``Iff && config.useRewrite then
    let { eNew, eqProof, mvarIds } ←
      mvarId.rewrite e (← lem.getValue) (symm := symm) config.toConfig
    let mp := if forwardImp then ``Eq.mp else ``Eq.mpr
    let impProof ← mkAppOptM mp #[e, eNew, eqProof]
    return { eNew, impProof, mvarIds }
  let r ← mvarId.grewriteImp e lem forwardImp config
  let mctx ← getMCtx
  let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
  return { r with mvarIds }

open Tactic

/-- Apply the `grewrite` tactic to the current goal. -/
def grewriteTarget' (stx : Syntax) (symm : Bool) (config : GRewrite.Config) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let target ← goal.getType
    let r ← elabGRewrite goal target stx (forwardImp := false) (symm := symm) (config := config)
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar r.eNew (← goal.getTag)
    goal.assign (mkApp r.impProof mvarNew)
    replaceMainGoal (mvarNew.mvarId! :: r.mvarIds)

/-- Apply the `grewrite` tactic to a local hypothesis. -/
def grewriteLocalDecl' (stx : Syntax) (symm : Bool) (fvarId : FVarId) (config : GRewrite.Config) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let type ← fvarId.getType
  let r ← elabGRewrite goal type stx (forwardImp := true) (symm := symm) (config := config)
  let proof := .app (r.impProof) (.fvar fvarId)
  let { mvarId, .. } ← goal.replace fvarId proof r.eNew
  replaceMainGoal (mvarId :: r.mvarIds)

/--
`grewrite [e]` is like `grw [e]`, but it doesn't try to close the goal with `rfl`.
This is analogous to `rw` and `rewrite`, where `rewrite` doesn't try to close the goal with `rfl`.
-/
syntax (name := grewriteSeq') "grewrite'" optConfig rwRuleSeq (location)? : tactic

@[tactic grewriteSeq', inherit_doc grewriteSeq'] def evalGRewriteSeq' : Tactic := fun stx => do
  let cfg ← elabGRewriteConfig stx[1]
  let loc := expandOptLocation stx[3]
  withRWRulesSeq stx[0] stx[2] fun symm term => do
    withLocation loc
      (grewriteLocalDecl' term symm · cfg)
      (grewriteTarget' term symm cfg)
      (throwTacticEx `grewrite · "did not find instance of the pattern in the current goal")

/--
`grw [e]` works just like `rw [e]`, but `e` can be a relation other than `=` or `↔`.

For example:

```lean
variable {a b c d n : ℤ}

example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [h₁, h₂]

example (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]

example (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  grw [h₁] at *
  exact h₂
```

To replace the RHS with the LHS of the given relation, use the `←` notation (just like in `rw`):

```
example (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  grw [← h₂, ← h₁]
```

The strict inequality `a < b` is turned into the non-strict inequality `a ≤ b` to rewrite with it.
A future version of `grw` may get special support for making better use of strict inequalities.

To rewrite only in the `n`-th position, use `nth_grw n`.
This is useful when `grw` tries to rewrite in a position that is not valid for the given relation.

To be able to use `grw`, the relevant lemmas need to be tagged with `@[gcongr]`.
To rewrite inside a transitive relation, you can also give it an `IsTrans` instance.

To let `grw` unfold more aggressively, as in `erw`, use `grw (transparency := default)`.
-/
macro (name := grwSeq) "grw' " c:optConfig s:rwRuleSeq l:(location)? : tactic =>
  match s with
  | `(rwRuleSeq| [$rs,*]%$rbrak) =>
    -- We show the `rfl` state on `]`
    `(tactic| (grewrite' $c [$rs,*] $(l)?; with_annotate_state $rbrak (try (with_reducible rfl))))
  | _ => Macro.throwUnsupported

end Mathlib.Tactic.GRewrite
