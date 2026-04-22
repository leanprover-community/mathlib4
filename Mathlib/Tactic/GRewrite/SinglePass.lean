/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GRewrite.Core
public meta import Lean.Elab.Tactic.Rewrite

/-!
# The generalized rewriting tactic 2.0
-/

meta section


namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

initialize registerTraceClass `Meta.grewrite
initialize registerTraceClass `Meta.grewrite.gcongr (inherited := true)

structure GRewriteLemma where
  symm : Bool
  levelParams : Array Name := #[]
  proof : Expr
  numHyps? : Option Nat
  headIdx : HeadIndex
  headNumArgs : Nat
  relName : Name

abbrev GRewriteM := ReaderT GRewriteLemma
  StateRefT (Std.HashSet (Option Expr × Expr × Bool)) GCongr.GCongrM

def GRewriteLemma.getValue (lem : GRewriteLemma) : MetaM Expr := do
  let us ← lem.levelParams.mapM fun _ => mkFreshLevelMVar
  return lem.proof.instantiateLevelParamsArray lem.levelParams us

def GRewriteLemma.metaTelescope (lem : GRewriteLemma) : MetaM (Array Expr × Expr × Expr) := do
  let proof ← lem.getValue
  let (mvars, _, rel) ← forallMetaTelescopeReducing (← inferType proof) lem.numHyps?
  -- Use `Expr.beta` to get nicer looking proof terms.
  return (mvars, rel, proof.beta mvars)

def GRewriteLemma.apply (lem : GRewriteLemma) (g : MVarId) (symm : Bool) (config : Config) :
    MetaM (Option (Array MVarId)) := do
  withTraceNode `Meta.grewrite (fun _ ↦ return m!"applying grewrite lemma `{lem.proof}`") do
  let (mvars, rel, proof) ← lem.metaTelescope
  let (rel, proof) ←
    if symm then
      let proof ← try proof.applySymm catch _ => return none
      pure (← inferType proof, proof)
    else
      pure (rel, proof)
  let applied ← withConfig (fun oldConfig => { config, oldConfig with }) do
    if ← isDefEq (← g.getType) rel then
      g.assign proof; return true
    else
      let mctx ← getMCtx
      for (n, tac) in (forwardExt.getState (← getEnv)).2 do
        if n matches ``GCongr.exact | ``GCongr.symmExact | ``GCongr.exactRefl then continue
        try tac.eval proof g; return true
        catch _ => setMCtx mctx
      return false
  unless applied do return none
  return some <| ← mvars.filterMapM fun mvar ↦ do
    if ← mvar.mvarId!.isAssigned then return none
    let type ← mvar.mvarId!.getType
    if (← isClass? type).isSome then
      if let some inst ← synthInstance? type then
        mvar.mvarId!.assign inst
        return none
    return mvar.mvarId!

def makeGCongrGoal (rel? : Option Expr) (e : Expr) (inv : Bool) : MetaM (Expr × Expr) := do
  if let some rel := rel? then
    -- Assume that `rel` is not heterogenous.
    let mvar ← mkFreshExprMVar (← inferType e)
    return (mvar, (if inv then mkApp2 rel mvar e else mkApp2 rel e mvar))
  else
    let mvar ← mkFreshExprMVar (Expr.sort 0)
    return (mvar, if inv then .forallE `_a mvar e .default else .forallE `_a e mvar .default)

def getRel' (e : Expr) : Option (Name × Option Expr × Expr × Expr) :=
  match e with
  | .app (.app rel lhs) rhs => rel.getAppFn.constName?.map (·, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (`_Implies, none, lhs, rhs)
    else
      none
  | _ => none

mutual

partial def processGCongrHypothesis (g : MVarId) (inv : Bool) (config : Config) :
    GRewriteM Bool := g.withContext do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← g.getType)) |
    throwError "invalid `gcongr` goal {g}"
  let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
  if let some (result, proof) ← grewriteCore relName rel? lhs inv config then
    rhs.withApp fun mvar xs ↦ do
      mvar.mvarId!.assign (← mkLambdaFVars xs result)
      g.assign proof
      return true
  else
    return false

partial def processGCongrLemma (g : MVarId) (lem : GCongrLemma) (inv : Bool)
    (config : Config) : GRewriteM Bool := do
  withTraceNode `Meta.grewrite.gcongr (fun _ ↦ return m!"applying {.ofConstName lem.declName}") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma g lem catch _ => return false
  /- Firstly, synthesize instances to ensure that the lemma is applicable in this setting.
  We allow synthesis to get stuck, because there are still metavariables to be filled in. -/
  let mut unsolvedSideGoals := #[]
  for mvarId in sideGoals do
    let type ← mvarId.getType
    if (← isClass? type).isSome then
      match ← trySynthInstance type with
      | .some inst => mvarId.assign inst; continue
      | .none => return false
      | .undef => pure ()
    unsolvedSideGoals := unsolvedSideGoals.push mvarId
    pushNewGoal mvarId
  -- Then, recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (g, isContra) in mainGoals do
    if ← processGCongrHypothesis g (inv != isContra) config then
      anyProgress := true
    else
      try g.applyRflOrId
      catch _ =>
        trace[Meta.grewrite] "{← g.getType} could not be closed with `rfl`"
        return false
  -- Only continue if at least one rewrite happened
  unless anyProgress do return false
  -- Finally, close all remaining side goals
  for mvarId in unsolvedSideGoals do
    let type ← mvarId.getType
    if (← isClass? type).isSome then
      let some inst ← synthInstance? type | return false
      mvarId.assign inst
    else
      let mctx ← getMCtx
      try GCongr.gcongrDischarger (← mvarId.intros).2
      catch _ => setMCtx mctx
  return true

partial def grewriteCore (relName : Name) (rel? : Option Expr) (e : Expr) (inv : Bool)
    (config : Config) : GRewriteM (Option (Expr × Expr)) := do
  withTraceNodeBefore `Meta.grewrite (fun _ ↦
    return m!"visiting `{e}` with relation `{rel?.elim m!"→" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, inv)
  if (← get).contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return none
  let (mvar, target) ← makeGCongrGoal rel? e inv
  let g ← mkFreshExprMVar target
  -- Try the given grewrite lemma.
  let lem ← read
  if e.toHeadIndex == lem.headIdx && e.headNumArgs == lem.headNumArgs then
    if let some goals ← lem.apply g.mvarId! (inv != lem.symm) config then
      goals.forM (pushNewGoal ·)
      return (mvar, g)
  -- Try all applicable `@[gcongr]` lemmas.
  if let some (head, args) := getCongrAppFnArgs e then
    let key := { relName, head, arity := args.size }
    let lemmas := ((gcongrExt.getState (← getEnv)).get? key).getD (relImpRelLemma args.size)
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if gcongrLem.forGrw then
        if ← processGCongrLemma g.mvarId! gcongrLem inv config then
          return (← instantiateMVars mvar, g)
        setMCtx mctx
  -- Cache the fact that there are no applicable lemmas
  modify (·.insert cacheKey)
  return none

end

def _root_.Lean.MVarId.grewrite (goal : MVarId) (e : Expr) (lem : GRewriteLemma)
    (forwardImp : Bool) (config : Config) : MetaM GRewriteResult :=
  withReducible do goal.withContext do
    goal.checkNotAssigned `grewrite
    if let (some (eNew, impProof), newGoals) ←
      grewriteCore `_Implies none e (!forwardImp) config |>.run lem |>.run' {} |>.run then
      let mvarIds ← newGoals.toList.filterM (not <$> ·.isAssigned)
      return { eNew, impProof, mvarIds }
    else
      let (_, rel, _) ← lem.metaTelescope
      let some (_, lhs, rhs) := getRel (← whnf rel) | unreachable!
      let pattern := if lem.symm then rhs else lhs
      throwTacticEx `grewrite goal
        m!"Did not find a suitable occurrence of {indentExpr pattern}\n\
        in the target expression{indentExpr e}"

open Lean Meta Elab Parser

def elabGRewriteLemma (stx : Syntax) (symm : Bool) (config : Config) :
    TermElabM GRewriteLemma := do
  Term.withoutModifyingElabMetaStateWithInfo do
  -- Fully elaborate `stx`, not allowing e.g any postponed `by` blocks.
  let e ← Term.elabTerm stx none
  Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
  let e ← instantiateMVars e
  if e.hasSyntheticSorry then
    throwAbortTactic
  withReducible do
  -- When using `apply_rw`, restrict the depth of the forall telescope.
  let type ← inferType e
  let numHyps? ←
    if config.implicationHyp then
      if let arity + 1 := type.getForallArity then
        pure (some arity)
      else
        throwError m!"Invalid apply_rw argument: Expected an implication, not {type}"
    else
      pure none
  let (mvars, _, rel) ← forallMetaTelescopeReducing (← inferType e) numHyps?
  -- Since `a ≥ b` gets reduced to `b ≤ a`, we need to flip the rewrite direction.
  let backward := rel.getAppFn'.constName?.any
    (· matches ``GE.ge | ``GT.gt | ``Superset | ``SSuperset)
  let symm := symm != backward
  let some (relName, lhs, rhs) := getRel (← whnf rel) |
    let valueDescr := if (← Meta.isProp rel) then "a proof of" else "a value of type"
    throwError m!"Invalid grewrite argument: Expected a relation or definition name, \
      but{inlineExpr (e.beta mvars)}is {valueDescr}{indentExpr rel}"
  -- Just like in `rw`, The head index and number of arguments determine where we try to rewrite.
  let (headIdx, headNumArgs) :=
    if symm then (rhs.toHeadIndex, rhs.headNumArgs) else (lhs.toHeadIndex, lhs.headNumArgs)
  if headIdx matches .mvar _ then
    throwError "Invalid grewrite argument: The pattern to be substituted \
      is a metavariable (`{lhs}`) in this relation{indentExpr rel}"
  let (levelParams, proof) ←
    if e.hasMVar then
      let r ← abstractMVars e
      pure (r.paramNames, r.expr)
    else
      pure (#[], e)
  return { symm, levelParams, proof, numHyps?, headIdx, headNumArgs, relName }

public def elabGRewrite (mvarId : MVarId) (e : Expr) (stx : Syntax) (forwardImp symm : Bool)
    (config : Config) : Tactic.TacticM GRewriteResult := do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let lem ← elabGRewriteLemma stx (symm := symm) (config := config)
  if lem.relName matches ``Eq | ``Iff && config.useRewrite then
    -- Elaborate `stx` again, so that we can use `Term.withSynthesize`
    let { eNew, eqProof, mvarIds } ← Term.withSynthesize <| Tactic.elabRewrite mvarId e stx symm
    let mp := if forwardImp then ``Eq.mp else ``Eq.mpr
    let impProof ← mkAppOptM mp #[e, eNew, eqProof]
    return { eNew, impProof, mvarIds }
  let r ← mvarId.grewrite e lem forwardImp config
  let mctx ← getMCtx
  let mvarIds := r.mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved
  return { r with mvarIds }

open Tactic

end Mathlib.Tactic.GRewrite
