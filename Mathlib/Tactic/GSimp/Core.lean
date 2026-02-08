/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GSimp.Types

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
    let (lhs, rhs) := if (← readThe Context).inv then (rhs, lhs) else (lhs, rhs)
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
partial def tryGCongrTheorem? (lem : GCongr.GCongrLemma) (e rel : Expr) (inv : Bool) :
    GSimpM (Option Result) := withNewMCtxDepth do
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
  let (lhs, rhs) := if inv then (rhs, lhs) else (lhs, rhs)
  unless ← isDefEq lhs e do
    return none
  for x in xs, bi in bis, i in 0...* do
    if !(← x.mvarId!.isAssigned) && !lem.mainSubgoals.any (·.1 == i) then
      let type ← x.mvarId!.getType
      if bi.isInstImplicit then
        if let .some inst ← trySynthInstance type then
          if ← withReducibleAndInstances (isDefEq inst x) then
            continue
      if ← isProp type then
        if let some proof ← (← getMethods).discharge? type then
          if ← isDefEq x proof then
            continue
      return none

  let mut modified := false
  for (i, numIntro, isContra) in lem.mainSubgoals do
    withTheReader MethodsRef (fun ctx ↦ { ctx with inv := ctx.inv != isContra }) do
    let h := xs[i]!
    let hType ← instantiateMVars (← inferType h)
    try
      if ← processGCongrSubgoal h hType numIntro then
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


partial def gsimpStep (e rel : Expr) (relName : Name) (idx : CacheIndex) (inv : Bool) :
    GSimpM Result := do
  let e ← instantiateMVars e
  match e with
  | .mdata m e => let r ← gsimp e rel relName idx inv; return { r with expr := mkMData m r.expr }
  | _ =>
  let some (head, args) := GCongr.getCongrAppFnArgs e | return { expr := e }
  let key : GCongr.GCongrKey := { relName, head, arity := args.size }
  let some lemmas := (← getGCongrTheorems)[key]? | return { expr := e }
  for lem in lemmas do
    if let some r ← tryGCongrTheorem? lem e rel inv then
      return r
  -- TODO: also do the `rel_imp_rel` lemma
  return { expr := e }


/-- A copy of `Simp.cacheResult`. -/
partial def cacheResult (idx : CacheIndex) (e : Expr) (r : Result) : GSimpM Result := do
  modify fun s => { s with cache := s.cache.insert idx e r }
  return r

/-- A copy of `Simp.simpLoop`. -/
partial def gsimpLoop (e rel : Expr) (relName : Name) (idx : CacheIndex)
    (inv : Bool) : GSimpM Result := withIncRecDepth do
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
      (← r.mkTrans e rel inv idx (← gsimpLoop r.expr rel relName idx inv))
    | .continue none => visitPreContinue cfg { expr := e }
    | .continue (some r) => visitPreContinue cfg r
where
  visitPreContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let r ← r.mkTrans e rel inv idx (← gsimpStep r.expr rel relName idx inv)
    visitPost cfg r
  visitPost (cfg : Config) (r : Result) : GSimpM Result := do
    match (← post r.expr) with
    | .done r' => cacheResult idx e (← r.mkTrans e rel inv idx r')
    | .continue none => visitPostContinue cfg r
    | .visit r' | .continue (some r') => visitPostContinue cfg (← r.mkTrans e rel inv idx r')
  visitPostContinue (cfg : Config) (r : Result) : GSimpM Result := do
    let mut r := r
    unless cfg.singlePass || e == r.expr do
      r ← r.mkTrans e rel inv idx (← gsimpLoop r.expr rel relName idx inv)
    cacheResult idx e r

partial def gsimp (e rel : Expr) (relName : Name) (idx : CacheIndex)
    (inv : Bool) : GSimpM Result := withIncRecDepth do
  checkSystem "gsimp"
  gsimpLoop e rel relName idx inv

end

def mainCore (e : Expr) (ctx : Context) (s : State) (methods : Methods) (inv : Bool) :
    MetaM Result := do
  GSimpM.run ctx s methods <| gsimp e default `_Implies 0 inv

end Mathlib.Tactic.GSimp
