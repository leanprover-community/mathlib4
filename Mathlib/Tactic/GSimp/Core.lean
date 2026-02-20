/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Rewrite
public import Mathlib.Tactic.GCongr.Core

/-!
# generalized rewriting

This module implements the generalized rewriting similar to how `simp` is implemented,
hence this will be called the `gsimp` tactic.
-/

public meta section

namespace Mathlib.Tactic.GSimp
open Lean Meta

mutual

/-- Process the given congruence theorem hypothesis. Return true if it made "progress". -/
partial def processGCongrSubgoal (h : Expr) (hType : Expr) (numIntro : Nat) :
    GSimpM Bool := do
  forallBoundedTelescope hType numIntro fun xs hType =>
    (if xs.isEmpty then id else withFreshCache) do
    let (idx, relName, rel, lhs, rhs) ← match hType with
      | .forallE _ lhs rhs _ => pure (0, `_Implies, default, lhs, rhs)
      | mkApp2 rel lhs rhs => pure (← getCacheIdx rel, rel.getAppFn.constName, rel, lhs, rhs)
      | _ => throwError "invalid `gcongr` subgoal {hType}"
    let (lhs, rhs) := if ← isInv then (rhs, lhs) else (lhs, rhs)
    let lhs ← instantiateMVars lhs
    let r ← gsimp lhs rel relName idx
    rhs.withApp fun m zs => do
      unless zs.all (·.isFVar) do failure -- TODO: this should be checked by `@[gcongr]`
      let val ← mkLambdaFVars zs r.expr
      unless (← isDefEq m val) do
        failure
      let proof ← r.getProof rel idx
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        failure
      return r.proof?.isSome

/-- Try to rewrite `e` children using the given gcongr lemma. -/
partial def tryGCongrTheorem? (lem : GCongr.GCongrLemma) (e rel : Expr) : GSimpM (Option Result) :=
  withNewMCtxDepth do
  trace[Debug.gsimp.congr] "{lem.declName}, {e}"
  let thm ← mkConstWithFreshMVarLevels lem.declName
  let type ← inferType thm
  let (xs, bis, type) ← withDefault <| forallMetaTelescopeReducing type lem.numHyps
  let (lhs, rhs) ← match type with
    | .forallE _ lhs rhs _ => pure (lhs, rhs)
    | mkApp2 rel' lhs rhs =>
      if ← isDefEq rel rel' then
        pure (lhs, rhs)
      else
        return none
    | _ => throwError "invalid `gcongr` theorem {lem.declName}`"
  let (lhs, rhs) := if ← isInv then (rhs, lhs) else (lhs, rhs)
  unless ← isDefEq lhs e do
    return none
  -- First, ensure that all side goals can be solved
  for x in xs, bi in bis, i in 0...* do
    if !(← x.mvarId!.isAssigned) && !lem.mainSubgoals.any (·.1 == i) then
      let type ← x.mvarId!.getType
      if bi.isInstImplicit then
        if let .some val ← trySynthInstance type then
          if ← withReducibleAndInstances (isDefEq x val) then
            continue
      if ← isProp type then
        if let some proof ← (← getMethods).discharge? type then
          if ← isDefEq x proof then
            continue
      return none
  -- Then, recurse into the subexpressions
  let mut modified := false
  for (i, numIntro, isContra) in lem.mainSubgoals do
    let h := xs[i]!
    let hType ← instantiateMVars (← inferType h)
    try
      if ← withContra isContra <| processGCongrSubgoal h hType numIntro then
        modified := true
    catch _ =>
      trace[gsimp.congr] "processCongrHypothesis {lem.declName} failed {hType}"
      return none
  unless modified do
    trace[gsimp.congr] "{lem.declName} not modified"
    return none
  let eNew ← instantiateMVars rhs
  let mut proof ← instantiateMVars (mkAppN thm xs)
  if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
    trace[gsimp.congr] "{lem.declName} has unassigned metavariables"
    return none
  return some { expr := eNew, proof? := proof }


partial def gsimpStep (e rel : Expr) (relName : Name) (idx : CacheIndex) : GSimpM Result := do
  let e ← instantiateMVars e
  match e with
  | .mdata m e => let r ← gsimp e rel relName idx; return { r with expr := mkMData m r.expr }
  | _ =>
  let some (head, args) := GCongr.getCongrAppFnArgs e | return { expr := e }
  let key : GCongr.GCongrKey := { relName, head, arity := args.size }
  let some lemmas := (← getGCongrTheorems)[key]? | return { expr := e }
  for lem in lemmas do
    if let some r ← tryGCongrTheorem? lem e rel then
      return r
  -- TODO: also do the `rel_imp_rel` lemma
  return { expr := e }


/-- A copy of `Simp.cacheResult`. -/
partial def cacheResult (idx : CacheIndex) (e : Expr) (r : Result) : GSimpM Result := do
  modify fun s => { s with cache := s.cache.insert idx e r }
  return r

/-- A copy of `Simp.simpLoop`. -/
partial def gsimpLoop (e rel : Expr) (relName : Name) (idx : CacheIndex) : GSimpM Result :=
  withIncRecDepth do
  let cfg ← getConfig
  let cache := (← get).cache
  if let some result := cache.find? idx e then
    return result
  if (← get).numSteps > cfg.maxSteps then
    throwError "`gsimp` failed: maximum number of steps exceeded"
  else
    checkSystem "gsimp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult idx e r
    | .visit r => cacheResult idx e <|
      (← r.mkTrans e rel idx (← gsimpLoop r.expr rel relName idx))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let r ← r.mkTrans e rel idx (← gsimpStep r.expr rel relName idx)
    visitPost cfg r
  visitPost (cfg : Config) (r : Result) : GSimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult idx e (← r.mkTrans e rel idx r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkTrans e rel idx r')
  visitPostContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkTrans e rel idx (← gsimpLoop r.expr rel relName idx)
    cacheResult idx e r

partial def gsimp (e rel : Expr) (relName : Name) (idx : CacheIndex) : GSimpM Result :=
  withIncRecDepth do
  checkSystem "gsimp"
  gsimpLoop e rel relName idx

end

def mainCore (e : Expr) (ctx : Context) (methods : Methods) :
    MetaM Result := do
  GSimpM.run ctx {} methods <| gsimp e default `_Implies 0

def defaultDischarger (e : Expr) : MetaM (Option Expr) := do
  let mvar ← mkFreshExprMVar e
  try
    GCongr.gcongrDischarger (← mvar.mvarId!.intros).2
    instantiateMVars mvar
  catch _ =>
    return none

set_option linter.style.longLine false

def gsimpCore (e : Expr) (ctx : Context) (discharge? : Option Discharge := none) : MetaM Result := do
  mainCore e ctx (GSimp.mkMethods (discharge?.getD defaultDischarger))









-- TODO: the following are all wrong, because they are copied from simp:


/--
Convert the given goal `Ctx |- target` into `Ctx |- targetNew` using an implication proof
`eqProof : target = targetNew`. It assumes `eqProof` has type `targetNew → target` -/
def _root_.Lean.MVarId.replaceTargetImp (mvarId : MVarId) (targetNew : Expr) (impProof : Expr) : MetaM MVarId := do
    mvarId.checkNotAssigned `replaceTarget
    let tag      ← mvarId.getTag
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    mvarId.assign (.app impProof mvarNew)
    return mvarNew.mvarId!

/--
Auxiliary method.
Given the current `target` of `mvarId`, apply `r` which is a new target and proof that it is equal to the current one.
-/
def applyGSimpResultToTarget (mvarId : MVarId) (target : Expr) (r : Result) : MetaM MVarId := do
  match r.proof? with
  | some proof => mvarId.replaceTargetImp r.expr proof
  | none =>
    if target != r.expr then
      mvarId.replaceTargetDefEq r.expr
    else
      return mvarId

/-- See `simpTarget`. This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def gsimpTargetCore (mvarId : MVarId) (ctx : Context) (discharge? : Option Discharge := none)
    (mayCloseGoal := true) : MetaM (Option MVarId) := do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← gsimpCore target { ctx with inv := true } discharge?
  if mayCloseGoal && r.expr.isTrue then
    match r.proof? with
    | some proof => mvarId.assign (.app proof (mkConst ``True.intro))
    | none => mvarId.assign (mkConst ``True.intro)
    return none
  else
    applyGSimpResultToTarget mvarId target r

/--
Gsimplify the given goal target (aka type). Return `none` if the goal was closed. Return `some mvarId'` otherwise,
where `mvarId'` is the simplified new goal. -/
def gsimpTarget (mvarId : MVarId) (ctx : Context) (discharge? : Option Discharge := none)
    (mayCloseGoal := true) : MetaM (Option MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `gsimp
    gsimpTargetCore mvarId ctx discharge? mayCloseGoal



/--
Applies the result `r` for `type` (which is inhabited by `val`). Returns `none` if the goal was closed. Returns `some (val', type')`
otherwise, where `val' : type'` and `type'` is the simplified `type`.

This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
def applyGSimpResult (mvarId : MVarId) (val : Expr) (r : Result) (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
  if mayCloseGoal && r.expr.isFalse then
    match r.proof? with
    | some eqProof => mvarId.assign (← mkFalseElim (← mvarId.getType) (.app eqProof val))
    | none => mvarId.assign (← mkFalseElim (← mvarId.getType) val)
    return none
  else
    match r.proof? with
    | some eqProof =>
      return some (.app eqProof val, r.expr)
    | none =>
      return some (val, r.expr)

-- def applyGSimpResultToFVarId (mvarId : MVarId) (fvarId : FVarId) (r : Result) (mayCloseGoal : Bool) : MetaM (Option (Expr × Expr)) := do
--   applyGSimpResult mvarId (mkFVar fvarId) r mayCloseGoal

-- /--
-- Simplify `prop` (which is inhabited by `proof`). Return `none` if the goal was closed. Return `some (proof', prop')`
-- otherwise, where `proof' : prop'` and `prop'` is the simplified `prop`.

-- This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
-- def gsimpStep' (mvarId : MVarId) (proof : Expr) (prop : Expr) (ctx : Context) (discharge? : Option Discharge := none)
--     (mayCloseGoal := true) : MetaM (Option (Expr × Expr)) := do
--   let r ← gsimpCore prop ctx discharge?
--   applyGSimpResult mvarId proof r (mayCloseGoal := mayCloseGoal)



-- def applyGSimpResultToLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (r : Option (Expr × Expr)) : MetaM (Option (FVarId × MVarId)) := do
--   match r with
--   | none => return none
--   | some (value, type') =>
--     let localDecl ← fvarId.getDecl
--     if localDecl.type != type' then
--       let mvarId ← mvarId.assert localDecl.userName type' value
--       let mvarId ← mvarId.tryClear localDecl.fvarId
--       let (fvarId, mvarId) ← mvarId.intro1P
--       return some (fvarId, mvarId)
--     else
--       return some (fvarId, mvarId)

-- /--
-- Simplify `simp` result to the given local declaration. Return `none` if the goal was closed.
-- This method assumes `mvarId` is not assigned, and we are already using `mvarId`s local context. -/
-- def applyGSimpResultToLocalDecl (mvarId : MVarId) (fvarId : FVarId) (r : Result) (mayCloseGoal : Bool) : MetaM (Option (FVarId × MVarId)) := do
--   if r.proof?.isNone then
--     -- New result is definitionally equal to input. Thus, we can avoid creating a new variable if there are dependencies
--     let mvarId ← mvarId.replaceLocalDeclDefEq fvarId r.expr
--     if mayCloseGoal && r.expr.isFalse then
--       mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
--       return none
--     else
--       return some (fvarId, mvarId)
--   else
--     applyGSimpResultToLocalDeclCore mvarId fvarId (← applyGSimpResultToFVarId mvarId fvarId r mayCloseGoal)

-- def gsimpLocalDecl (mvarId : MVarId) (fvarId : FVarId) (ctx : Context) (discharge? : Option Discharge := none)
--     (mayCloseGoal := true) : MetaM (Option (FVarId × MVarId)) := do
--   mvarId.withContext do
--     mvarId.checkNotAssigned `simp
--     let type ← instantiateMVars (← fvarId.getType)
--     let r ← gsimpStep' mvarId (mkFVar fvarId) type ctx discharge? mayCloseGoal
--     return ← applyGSimpResultToLocalDeclCore mvarId fvarId r


def gsimpGoal (mvarId : MVarId) (ctx : Context) (discharge? : Option Discharge := none)
    (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) :
    MetaM (Option (Array FVarId × MVarId)) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `simp
    let mut mvarIdNew := mvarId
    let mut toAssert := #[]
    let mut replaced := #[]
    for fvarId in fvarIdsToSimp do
      let localDecl ← fvarId.getDecl
      let type ← instantiateMVars localDecl.type
      let ctx := { ctx with gsimpTheorems.erased := ctx.gsimpTheorems.erased.insert (.fvar localDecl.fvarId) }
      let r ← gsimpCore type ctx discharge?
      match r.proof? with
      | some _ => match ← applyGSimpResult mvarIdNew (mkFVar fvarId) r with
        | none => return none
        | some (value, type) => toAssert := toAssert.push { userName := localDecl.userName, type := type, value := value }
      | none =>
        if r.expr.isFalse then
          mvarIdNew.assign (← mkFalseElim (← mvarIdNew.getType) (mkFVar fvarId))
          return none
        -- TODO: if there are no forwards dependencies we may consider using the same approach we used when `r.proof?` is a `some ...`
        -- Reason: it introduces a `mkExpectedTypeHint`
        mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
        replaced := replaced.push fvarId
    if simplifyTarget then
      match (← gsimpTarget mvarIdNew ctx discharge?) with
      | none => return none
      | some mvarIdNew' => mvarIdNew := mvarIdNew'
    let (fvarIdsNew, mvarIdNew') ← mvarIdNew.assertHypotheses toAssert
    mvarIdNew := mvarIdNew'
    let toClear := fvarIdsToSimp.filter fun fvarId => !replaced.contains fvarId
    mvarIdNew ← mvarIdNew.tryClearMany toClear
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`simp` made no progress"
    return some (fvarIdsNew, mvarIdNew)

-- def simpTargetStar (mvarId : MVarId) (ctx : Context) (discharge? : Option Discharge := none) :
--     MetaM TacticResultCNM := mvarId.withContext do
--   let mut ctx := ctx
--   for h in (← getPropHyps) do
--     let localDecl ← h.getDecl
--     let proof  := localDecl.toExpr
--     let gsimpTheorems ← ctx.gsimpTheorems.addTheorem (.fvar h) proof (config := ctx.indexConfig)
--     ctx := { ctx with gsimpTheorems }
--   match (← gsimpTarget mvarId ctx discharge?) with
--   | none => return TacticResultCNM.closed
--   | some mvarId' =>
--     if (← mvarId.getType) == (← mvarId'.getType) then
--       return TacticResultCNM.noChange
--     else
--       return TacticResultCNM.modified mvarId'

end Mathlib.Tactic.GSimp
