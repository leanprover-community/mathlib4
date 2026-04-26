/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
module

public meta import Lean.Meta.Tactic.Rewrite
public import Mathlib.Tactic.GCongr.Core

/-!

# The generalized rewriting tactic

This module defines the core of the `grw`/`grewrite` tactic.

TODO:

The algorithm used to implement `grw` uses the same method as `rw` to determine where to rewrite.
This means that we can get ill-typed results. Moreover, it doesn't detect which occurrences
can be rewritten by `gcongr` and which can't. It also means we cannot rewrite bound variables.

A better algorithm would be similar to `simp only`, where we recursively enter the subexpression
using `gcongr` lemmas. This is tricky due to the many different `gcongr` for each pattern.

With the current implementation, we can instead use `nth_grw`.

-/

public meta section

namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

/-- Given a proof of `a ~ b`, close a goal of the form `a ~' b` or `b ~' a`
for some possibly different relation `~'`. -/
def dischargeMain (hrel : Expr) (goal : MVarId) : MetaM Bool := do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"

/-- The result returned by `Lean.MVarId.grewrite`. -/
structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals

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

inductive Progress where
  | none
  | matched
  | matchedOutOfScope

structure State where
  cache : Std.HashSet (Option Expr × Expr × Bool) := {}
  progress : Progress := .none

structure GRewriteLemma where
  symm : Bool
  proof : Expr
  type : Expr
  headIdx : HeadIndex
  headNumArgs : Nat
  mvarIds : Array (MVarId × Array LocalDecl)

abbrev GRewriteM := ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

def GRewriteLemma.apply (lem : GRewriteLemma) (g : MVarId) (symm : Bool)
    (config : GRewrite.Config) : MetaM Bool := do
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
      -- Exclude a few `gcongr_forward` extensions that are not relevant here.
      -- `@[gcongr_forward]` should probably be refactored anyways to not require meta code.
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
  if sameLCtx then
    processGCongrHypothesis g inv config
  else
    g.withContext do
    if (← get).progress matches .none then
      -- Hack: modify the local context of the metavariables
      let mctx ← getMCtx
      let lctx ← getLCtx
      setMCtx <| (← read).mvarIds.foldl (init := mctx) fun mctx (mvarId, decls) ↦
        let decl := mctx.getDecl mvarId
        let decl' := { decl with lctx := decls.foldl (·.addDecl ·) lctx }
        { mctx with decls := mctx.decls.insert mvarId decl' }
      let result ← processGCongrHypothesis g inv config
      if (← get).progress matches .none then setMCtx mctx
      return result
    else
      let result ← processGCongrHypothesis g inv config
      modify ({ · with progress := .matchedOutOfScope })
      return result

partial def processGCongrLemma (g : MVarId) (lem : GCongrLemma) (inv : Bool)
    (config : Config) : GRewriteM Bool := do
  withTraceNode `Meta.grewrite (fun _ ↦
    return m!"applying `gcongr` lemma {.ofConstName lem.declName}") do
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
    unless (← get).progress matches .matchedOutOfScope do
      if ← processGCongrHypothesisIntro g sameLCtx (inv != isContra) config then
        anyProgress := true
        continue
    try
      -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
      withReducibleAndInstances g.applyRflOrId
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

/--
Rewrite `e` using the relation `hrel : x ~ y`, and construct an implication proof
using the `gcongr` tactic to discharge this goal.

if `forwardImp = true`, we prove that `e → eNew`; otherwise `eNew → e`.

If `symm = false`, we rewrite `e` to `eNew := e[x/y]`; otherwise `eNew := e[y/x]`.

The code aligns with `Lean.MVarId.rewrite` as much as possible.
-/
def _root_.Lean.MVarId.grewrite (goal : MVarId) (e : Expr) (hrel : Expr)
    (mvarIds : Array (MVarId × Array LocalDecl)) (forwardImp symm : Bool)
    (config : GRewrite.Config) : MetaM GRewriteResult :=
  goal.withContext do
    goal.checkNotAssigned `grewrite
    let hrelType ← instantiateMVars (← inferType hrel)
    let maxMVars? ←
      if config.implicationHyp then
        if let arity + 1 := hrelType.getForallArity then
          pure (some arity)
        else
          throwTacticEx `apply_rw goal m!"invalid implication {hrelType}"
      else
        pure none
    let (newMVars, binderInfos, hrelType) ←
      withReducible <| forallMetaTelescopeReducing hrelType maxMVars?
    /- We don't reduce `hrelType` because if it is `a > b`, turning it into `b < a` would
    reverse the direction of the rewrite. However, we do need to clear metadata annotations. -/
    let hrelType := hrelType.cleanupAnnotations

    -- If we can use the normal `rewrite` tactic, we default to using that.
    if (hrelType.isAppOfArity ``Iff 2 || hrelType.isAppOfArity ``Eq 3) && config.useRewrite then
      let { eNew, eqProof, mvarIds } ← goal.rewrite e hrel symm config.toConfig
      let mp := if forwardImp then ``Eq.mp else ``Eq.mpr
      let impProof ← mkAppOptM mp #[e, eNew, eqProof]
      return { eNew, impProof, mvarIds }

    let hrelIn := hrel
    -- check that `hrel` proves a relation
    let hrel := mkAppN hrel newMVars
    let some (_, lhs, rhs) := GCongr.getRel hrelType |
      throwTacticEx `grewrite goal m!"{hrelType} is not a relation"
    let (pattern, replacement) := if symm then (rhs, lhs) else (lhs, rhs)
    if pattern.getAppFn.isMVar then
      throwTacticEx `grewrite goal
        m!"pattern is a metavariable{indentExpr pattern}\nfrom relation{indentExpr hrelType}"
    -- abstract the occurrences of `lhs` from `e` to get `eAbst`
    let e ← instantiateMVars e
    let (eNew, impProof, sideGoals) ←
      if config.useKAbstract then
        let eAbst ← withConfig ({ config, · with }) <| kabstract e pattern config.occs
        unless eAbst.hasLooseBVars do
          throwTacticEx `grewrite goal
            m!"did not find instance of the pattern in the target expression{indentExpr pattern}"
        -- construct `eNew` by instantiating `eAbst` with `replacement`.
        let eNew := eAbst.instantiate1 replacement
        let eNew ← instantiateMVars eNew
        -- check that `eNew` is well typed
        try
          check eNew
        catch ex =>
          throwTacticEx `grewrite goal m!"\
            rewritten expression is not type correct:{indentD eNew}\nError: {ex.toMessageData}\
            \n\n\
            Possible solutions: use grewrite's 'occs' configuration option \
            to limit which occurrences are rewritten, \
            or specify what the rewritten expression should be and use 'gcongr'."
        let eNew ← if replacement.hasBinderNameHint then eNew.resolveBinderNameHint else pure eNew
        -- Construct the implication proof using `gcongr`.
        -- Although `e` and `e'` are defEq, they may not be defEq in the `reducible` transparency.
        -- So, it is important to use `e'` in the `gcongr` goal.
        let e' := eAbst.instantiate1 (GCongr.mkHoleAnnotation pattern)
        let mkImp (e₁ e₂ : Expr) : Expr := .forallE `_a e₁ e₂ .default
        let imp := if forwardImp then mkImp e' eNew else mkImp eNew e'
        let gcongrGoal ← mkFreshExprMVar imp
        let (_, sideGoals) ← gcongrGoal.mvarId!.gcongr forwardImp
          |>.run (mainGoalDischarger := GRewrite.dischargeMain hrel)
        pure (eNew, gcongrGoal, sideGoals)
      else
        withReducible do
        let some (_, lhs', rhs') := GCongr.getRel (← whnf hrelType) |
          throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
        let mut symm := symm
        unless lhs' == lhs && rhs' == rhs do
          if lhs' == rhs && rhs' == lhs then
            symm := !symm
          else
            throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
        let (headIdx, headNumArgs) := (pattern.toHeadIndex, pattern.headNumArgs)
        let mvarIds := mvarIds ++ newMVars.map (·.mvarId!, #[])
        if let (some (eNew, impProof), newGoals) ←
          grewriteCore `_Implies none e (!forwardImp) config |>.run
            { symm, proof := hrel, type := hrelType, headIdx, headNumArgs, mvarIds }
            |>.run' {} |>.run then
          pure (eNew, impProof, newGoals)
        else
          throwTacticEx `grewrite goal
            m!"Did not find a suitable occurrence of {indentExpr pattern}\n\
            in the target expression{indentExpr e}"

    -- post-process the metavariables
    postprocessAppMVars `grewrite goal newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← (sideGoals ++ newMVars.map Expr.mvarId!).filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, impProof, mvarIds := newMVarIds.toList }

end Mathlib.Tactic.GRewrite
