/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Rewrite

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
    let (rel, lhs, rhs) ← match hType with
      | .forallE _ lhs rhs _ =>
        pure (none, lhs, rhs)
      | mkApp2 rel lhs rhs =>
        pure (some rel, lhs, rhs)
      | _ => throwError "invalid `gcongr` subgoal {hType}"
    withRel rel do
    let (lhs, rhs) := if ← isInv then (rhs, lhs) else (lhs, rhs)
    let lhs ← instantiateMVars lhs
    let r ← gsimp lhs
    logInfo m!"simplified to {r.expr} with proof {r.proof?}"
    rhs.withApp fun m zs => do
      unless zs.all (·.isFVar) do failure -- TODO: this should be checked by `@[gcongr]`
      let val ← mkLambdaFVars zs r.expr
      unless (← isDefEq m val) do
        failure
      let proof ← r.getProof
      unless (← isDefEq h (← mkLambdaFVars xs proof)) do
        logInfo m!"{h}, {xs}, {proof}"
        failure
      return r.proof?.isSome

/-- Try to rewrite `e` children using the given gcongr lemma. -/
partial def tryGCongrTheorem? (thm : Expr) (numHyps : Nat)
    (mainSubgoals : Array (Nat × Nat × Bool)) (e : Expr) :
    GSimpM (Option Result) := do
  let type ← inferType thm
  let (xs, bis, type) ← withDefault <| forallMetaTelescopeReducing type numHyps
  logInfo m!"{xs}, {type}"
  let (lhs, rhs) ← match type with
    | .forallE _ lhs rhs _ => pure (lhs, rhs)
    | mkApp2 rel' lhs rhs =>
      if let some rel ← getRel then
        if ← isDefEq rel rel' then
          pure (lhs, rhs)
        else
          return none
      else
        return none
    | _ => throwError "invalid `gcongr` theorem {thm}`"
  let (lhs, rhs) := if ← isInv then (rhs, lhs) else (lhs, rhs)
  unless ← isDefEq lhs e do
    return none
  -- First, ensure that all side goals can be solved
  for x in xs, bi in bis, i in 0...* do
    if !(← x.mvarId!.isAssigned) && !mainSubgoals.any (·.1 == i) then
      -- TODO: improve the detection of whether there are unsolved side goals
      -- The `gcongr` lemma should store which goals are side goals.
      let type ← x.mvarId!.getType
      if bi.isInstImplicit then
        if let .some val ← trySynthInstance type then
          if ← withReducibleAndInstances (isDefEq x val) then
            continue
      if ← isProp type then
        if let some proof ← (← getMethods).discharge? type then
          if ← isDefEq x proof then
            continue
        else
          return none
  -- Then, recurse into the subexpressions
  let mut modified := false
  for (i, numIntro, isContra) in mainSubgoals do
    let h := xs[i]!
    let hType ← instantiateMVars (← inferType h)
    try
      if ← withContra isContra <| processGCongrSubgoal h hType numIntro then
        modified := true
    catch e =>
      trace[Meta.Tactic.simp.congr] "processCongrHypothesis {thm} failed {hType}"
      logInfo m!"error {e.toMessageData}"
      return none
  unless modified do
    trace[Meta.Tactic.simp.congr] "{thm} not modified"
    return none
  let eNew ← instantiateMVars rhs
  let mut proof ← instantiateMVars (mkAppN thm xs)
  if (← hasAssignableMVar proof <||> hasAssignableMVar eNew) then
    trace[Meta.Tactic.simp.congr] "{thm} has unassigned metavariables"
    return none
  return some { expr := eNew, proof? := proof }

/-- Try to rewrite the goal using reflexivity or transitivity. -/
partial def tryBuiltinGSimpTheorems? (e : Expr) : GSimpM (Option Result) := do
  unless (← getRelName) == `_Implies do return none
  let mkApp2 rel lhs rhs := e | return none
  try
    withRel rel do
    let inv ← isInv
    -- reflexivity
    if inv then
      if ← isDefEq lhs rhs then
        return some {
          expr := mkConst ``True
          proof? := some <| .lam `t (mkConst ``True) ((← getRfl).app lhs) .default }
    let trans ← getTrans
    -- transitivity on the left
    let mvar ← mkFreshExprMVar (← getRelType)
    let thm := if inv then mkApp3 trans lhs mvar rhs else mkApp3 trans mvar lhs rhs
    if let some r ← tryGCongrTheorem? thm 1 #[(0, 0, true)] e then
      return some r
    -- transitivity on the right
    let mvar ← mkFreshExprMVar (← getRelType)
    let thm ← mkAppM ``flip
      #[if inv then mkApp3 trans lhs mvar rhs else mkApp3 trans mvar lhs rhs]
    if let some r ← tryGCongrTheorem? thm 1 #[(0, 0, false)] e then
      return some r
    return none
  catch _ =>
    return none

partial def gsimpStep (e : Expr) : GSimpM Result := do
  let e ← instantiateMVars e
  match e with
  | .mdata m e => let r ← gsimp e; return { r with expr := mkMData m r.expr }
  | _ => withNewMCtxDepth do

  let some (head, args) := GCongr.getCongrAppFnArgs e | return { expr := e }
  let key : GCongr.GCongrKey := { relName := ← getRelName, head, arity := args.size }
  let some lemmas := (← getGCongrTheorems)[key]? | return { expr := e }
  for lem in lemmas do
    let thm ← mkConstWithFreshMVarLevels lem.declName
    if let some r ← tryGCongrTheorem? thm lem.numHyps lem.mainSubgoals e then
      return r
  if let some r ← tryBuiltinGSimpTheorems? e then
    return r
  return { expr := e }


/-- A copy of `Simp.cacheResult`. -/
partial def cacheResult (e : Expr) (r : Result) : GSimpM Result := do
  let inv ← isInv
  modifyCacheEntry (·.insert inv e r)
  return r

/-- A copy of `Simp.simpLoop`. -/
partial def gsimpLoop (e : Expr) : GSimpM Result :=
  withIncRecDepth do
  let cfg ← getConfig
  let cache ← getCacheEntry
  if let some result := cache.find? (← isInv) e then
    return result
  if (← get).numSteps > cfg.maxSteps then
    throwError "`gsimp` failed: maximum number of steps exceeded"
  else
    checkSystem "gsimp"
    modify fun s => { s with numSteps := s.numSteps + 1 }
    match (← pre e) with
    | .done r  => cacheResult e r
    | .visit r => cacheResult e <|
      (← r.mkTrans e (← gsimpLoop r.expr))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let r ← r.mkTrans e (← gsimpStep r.expr)
    visitPost cfg r
  visitPost (cfg : Config) (r : Result) : GSimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult e (← r.mkTrans e r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkTrans e r')
  visitPostContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkTrans e (← gsimpLoop r.expr)
    cacheResult e r

partial def gsimp (e : Expr) : GSimpM Result :=
  withIncRecDepth do
  checkSystem "gsimp"
  gsimpLoop e

end

def mainCore (e : Expr) (ctx : Context) (methods : Methods) :
    MetaM Result := do
  GSimpM.run ctx {} methods <| gsimp e

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


-- TODO: move out to a common file to share code with `grw`.
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
      throwError "`gsimp` made no progress"
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
