/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GCongr.Core

/-!
# The generalized rewriting tactic 2.0
-/

public meta section


namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
structure Config extends Rewrite.Config where
  /-- When `useRewrite = true`, switch to using the default `rewrite` tactic when the goal is
  and equality or iff. -/
  useRewrite : Bool := true
  /-- When `implicationHyp = true`, interpret the rewrite rule as an implication. -/
  implicationHyp : Bool := false
  /-- Whether to use `kabstract` to find the rewrites locations. -/
  useKAbstract := false

initialize registerTraceClass `Meta.grewrite
initialize registerTraceClass `Meta.grewrite.gcongr (inherited := true)

inductive Progress where
  | none
  | matched
  | done

structure State where
  cache : Std.HashSet (Option Expr × Expr × Bool) := {}
  progress : Progress := .none

structure GRewriteLemma where
  symm : Bool
  proof : Expr
  type : Expr
  headIdx : HeadIndex
  headNumArgs : Nat
  relName : Name -- change to Bool for whether it is `Eq`/`Iff`.
  mvarIds : Array MVarId

abbrev GRewriteM := ReaderT GRewriteLemma
  StateRefT State GCongr.GCongrM

def GRewriteLemma.apply (lem : GRewriteLemma) (g : MVarId) (symm : Bool) (config : Config) :
    MetaM Bool := do
  withTraceNode `Meta.grewrite (fun _ ↦ return m!"applying grewrite lemma `{lem.proof}`") do
  let (rel, proof) ←
    if symm then
      let proof ← try lem.proof.applySymm catch _ => return false
      pure (← inferType proof, proof)
    else
      pure (lem.type, lem.proof)
  withConfig (fun oldConfig => { config, oldConfig with }) do
    if ← isDefEq (← g.getType) rel then
      g.assign proof
      return true
    let mctx ← getMCtx
    for (n, tac) in (forwardExt.getState (← getEnv)).2 do
      if n matches ``GCongr.exact | ``GCongr.symmExact | ``GCongr.exactRefl then continue
      try tac.eval proof g; return true
      catch _ => setMCtx mctx
    return false

def makeGCongrGoal (rel? : Option Expr) (e : Expr) (inv : Bool) : MetaM (Expr × Expr) := do
  if let some rel := rel? then
    -- Assume that the two arguments of `rel` have the same type.
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
    GRewriteM Bool := do
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

partial def processGCongrHypothesisIntro (g : MVarId) (sameLCtx : Bool) (inv : Bool)
    (config : Config) : GRewriteM Bool := do
  if sameLCtx then processGCongrHypothesis g inv config else
  if (← get).progress matches .matched then return false
  g.withContext do
  -- Hack: modify the local context of the metavariables in the given term
  let mctx ← getMCtx
  let lctx ← getLCtx
  setMCtx <| (← read).mvarIds.foldl (init := mctx) fun mctx mvarId ↦
    let decl := mctx.getDecl mvarId
    { mctx with decls := mctx.decls.insert mvarId { decl with lctx } }
  let result ← processGCongrHypothesis g inv config
  match (← get).progress with
  | .none => setMCtx mctx
  | .matched => modify ({ · with progress := .done })
  | .done => pure ()
  return result

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
  -- Then, recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (g, isContra, sameLCtx) in mainGoals do
    unless (← get).progress matches .done do
      if ← processGCongrHypothesisIntro g sameLCtx (inv != isContra) config then
        anyProgress := true
        continue
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
      dischargeSide mvarId
  return true

partial def grewriteCore (relName : Name) (rel? : Option Expr) (e : Expr) (inv : Bool)
    (config : Config) : GRewriteM (Option (Expr × Expr)) := do
  withTraceNodeBefore `Meta.grewrite (fun _ ↦
    return m!"visiting `{e}` in the {if inv then "rhs" else "lhs"} of relation \
      `{rel?.elim m!"→" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, inv)
  if (← get).cache.contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return none
  let (mvar, target) ← makeGCongrGoal rel? e inv
  let g ← mkFreshExprMVar target
  -- Try the given grewrite lemma.
  let lem ← read
  if e.toHeadIndex == lem.headIdx && e.headNumArgs == lem.headNumArgs then
    if ← lem.apply g.mvarId! (inv != lem.symm) config then
      modify ({ · with progress := .matched })
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
  modify fun s ↦ { s with cache := s.cache.insert cacheKey }
  return none

end

end Mathlib.Tactic.GRewrite
