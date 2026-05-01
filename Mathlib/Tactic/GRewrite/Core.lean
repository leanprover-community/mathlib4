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

This file provides two implementations of the tactic:
1. The simple implementation uses `kabstract` to determine where to rewrite,
   and then calls `MVarId.gcongr` to prove that the rewrite is valid.
   This is used by `nth_grw` and `grw'`
2. The more sophisticated implementation has its own congruence loop, applying `gcongr` lemmas to
   create the replacement expression, while at the same time proving that this is related to the
   original expression.
   This is used by `grw` and `apply_rw`.
-/

meta section

namespace Mathlib.Tactic.GRewrite

open Lean Meta GCongr

/-- The result returned by `Lean.MVarId.grewrite`. -/
public structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals

/-- Configures the behavior of the `rewrite` and `rw` tactics. -/
public structure Config extends Rewrite.Config where
  /-- When `useRewrite = true`, switch to using the default `rewrite` tactic when the goal is
  and equality or iff. -/
  useRewrite : Bool := true
  /-- When `implicationHyp = true`, interpret the rewrite rule as an implication. -/
  implicationHyp : Bool := false
  /-- Whether to use `kabstract` to find the rewrites locations. -/
  useKAbstract := false

section kabstract

/-- Given a proof of `a ~ b`, close a goal of the form `a ~' b` or `b ~' a`
for some possibly different relation `~'`. -/
def dischargeMain (hrel : Expr) (goal : MVarId) : MetaM Bool := do
  if ← goal.gcongrForward #[hrel] then
    return true
  else
    throwTacticEx `grewrite goal m!"could not discharge {← goal.getType} using {← inferType hrel}"

/-- Execute a generalized rewrite by first using `kabstract` to generate the replacement expression,
and then calling `gcongr` to prove that this is related to the original expression. -/
def grewriteUsingKAbstract (goal : MVarId) (e hrel pattern replacement : Expr)
    (forwardImp : Bool) (config : GRewrite.Config) : MetaM (Expr × Expr × Array MVarId) := do
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

end kabstract

section singlePass

initialize registerTraceClass `Meta.grewrite

/-- The congruence loop keeps track of its progress using 3 states. -/
inductive Progress where
  /-- The rewrite lemma has not unified with anything yet. -/
  | noMatch
  /-- The rewrite lemma has unified with something. -/
  | matched
  /-- The rewrite lemma has unified with something in a local context that is out of scope now. -/
  | matchedOutOfScope

/-- The state used in `GRewriteM`. -/
structure State where
  /-- The cache used in `grw` to avoid trying and failing to rewrite the same term multiple times.
  Each key stores the relation (`none` encodes the `→` relation), rewritten expression,
  and direction of the rewrite.
  This lets us avoid an exponential blowup when there are multiple `gcongr` lemmas for rewriting
  in the same place, such as `add_le_add`, `add_le_add_left` and `add_le_add_right`. -/
  cache : Std.HashSet (Option Expr × Expr × Bool) := {}
  /-- The current progress level. -/
  progress : Progress := .noMatch

/-- The information about the given rewrite lemma. -/
structure GRewriteLemma where
  /-- Whether the lemma rewrites right-to-left (i.e. whether it has a `←`). -/
  symm : Bool
  /-- The value -/
  proof : Expr
  /-- The type -/
  type : Expr
  /-- The key used to determine where to attempt rewriting. -/
  index : HeadIndex × Nat
  /-- The metavariables that appear in the lemma. We do the slightly dodgy thing of
  modifying their local context in order to be able to unify with bound variables. -/
  mvarIds : Array (MVarId × Array LocalDecl)

/-- The monad used for `grw`. -/
abbrev GRewriteM := ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

/-- Unify the given generalized rewrite lemma with the goal, so as to rewrite with it.
If `symm := true`, first use the `symm` tactic to swap the direction of the lemma.
`gcongr_forward` is used to deal with the case where the lemma is `a < b` and the goal is `a ≤ b`.
-/
def GRewriteLemma.apply (lem : GRewriteLemma) (goal : MVarId) (symm : Bool)
    (config : GRewrite.Config) : MetaM Bool := do
  withTraceNode `Meta.grewrite (fun _ ↦ return m!"rewriting with `{lem.proof}`") do
  let (type, proof) ←
    if symm then
      let proof ← try lem.proof.applySymm catch _ => return false
      pure (← inferType proof, proof)
    else
      pure (lem.type, lem.proof)
  withConfig (fun oldConfig => { config, oldConfig with }) do
  if ← isDefEq (← goal.getType) type then
    goal.assign proof
    return true
  let mctx ← getMCtx
  for (n, tac) in (forwardExt.getState (← getEnv)).2 do
    -- Explicitly exclude a few `gcongr_forward` extensions that are not relevant here.
    if n matches ``GCongr.exact | ``GCongr.symmExact | ``GCongr.exactRefl then continue
    try tac.eval proof goal; return true
    catch _ => setMCtx mctx
  return false

/-- Create the `gcongr` goal corresponding to rewriting `e` by relation `rel?`,
so that we can apply `gcongr` lemmas to it. -/
def makeGCongrGoal (rel? : Option Expr) (e : Expr) (inv : Bool) : MetaM (Expr × Expr) := do
  let mkRel := if let some rel := rel? then mkApp2 rel else (.forallE `_a · · .default)
  -- Assume that the two arguments of `rel` have the same type.
  let mvar ← mkFreshExprMVar (← inferType e)
  let target := if inv then mkRel mvar e else mkRel e mvar
  return (mvar, ← mkFreshExprMVar target)

/-- Version of `getRel` that also returns the expression of the relation. -/
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

/-- Recursively call `grewriteCore` to process a subgoal of a `gcongr` lemma. -/
partial def processGCongrHypothesisAux (goal : MVarId) (inv : Bool) (config : Config) :
    GRewriteM Bool := do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if inv then (rhs, lhs) else (lhs, rhs)
  if let some (result, proof) ← grewriteCore relName rel? target inv config then
    mvarApp.withApp fun mvar xs ↦ do
      mvar.mvarId!.assign (← mkLambdaFVars xs result)
      goal.assign proof
      return true
  else
    return false

/-- Update the local contexts of the metavariables to include the variables introduced by the
`gcongr` lemma. This is a bit of a hack. -/
partial def processGCongrHypothesis (goal : MVarId) (inv : Bool)
    (config : Config) : GRewriteM Bool := do
  -- If the local context was not changed, we don't need to modify the local contexts.
  if (← goal.getDecl).lctx.numIndices == (← getLCtx).numIndices then
    processGCongrHypothesisAux goal inv config
  else
  let outerLCtx ← getLCtx
  goal.withContext do
  -- We can only modify the metavariable local contexts if no match has happened yet.
  if (← get).progress matches .noMatch then
    let mctx ← getMCtx
    let lctx ← getLCtx
    setMCtx <| (← read).mvarIds.foldl (init := mctx) fun mctx (mvarId, decls) ↦
      -- Create a local context for `mvarId` by adding `decls` to the current local context.
      let lctx := decls.foldl (·.addDecl ·) lctx
      { mctx with decls := mctx.decls.insert mvarId { mctx.getDecl mvarId with lctx } }
    let result ← processGCongrHypothesisAux goal inv config
    if (← get).progress matches .noMatch then
      -- If we still don't have a match, then revert the changes to the metavaraible local contexts.
      setMCtx mctx
    else
      -- If we did get a match, then we might be exiting the scope where this rewrite makes sense,
      -- in which case we should not rewrite any more.
      let validInOuterLCtx ← (← read).mvarIds.allM fun (mvarId, _) ↦ do
        let some val ← getExprMVarAssignment? mvarId | return false
        return (Lean.collectFVars {} val).fvarIds.all outerLCtx.contains
      unless validInOuterLCtx do
        modify ({ · with progress := .matchedOutOfScope })
    return result
  else
    processGCongrHypothesisAux goal inv config

/-- Apply the `gcongr` lemma to the goal. The main subgoals are visited for rewriting in,
and otherwise closed `by rfl`. If at least one rewrite has happened, we commit to this lemma,
and we try to discharge the side goals. -/
partial def processGCongrLemma (goal : MVarId) (lem : GCongrLemma) (inv : Bool)
    (config : Config) : GRewriteM Bool :=
  withTraceNode `Meta.grewrite (fun _ ↦
    return m!"applying `gcongr` lemma {.ofConstName lem.declName}") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma goal lem catch _ => return false
  -- Recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (goal, isContra) in mainGoals do
    -- Any of the rewrites in this loop could make a match that is out of scope here.
    -- In that case we should stop rewriting, and the remaining goals should be closed `by rfl`.
    unless (← get).progress matches .matchedOutOfScope do
      if ← processGCongrHypothesis goal (inv != isContra) config then
        anyProgress := true
        continue
    try
      -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
      withReducibleAndInstances goal.applyRflOrId
    catch ex =>
      -- In principle, this case should not happen.
      trace[Meta.grewrite] "{← goal.getType} could not be closed with `rfl`:\n{ex.toMessageData}"
      return false
  -- Only continue if at least one rewrite happened
  unless anyProgress do return false
  -- Finally, run the discharger on the side goals.
  for mvarId in sideGoals do
    let type ← mvarId.getType
    -- There may be instance side goals that still had metavariables before recursively rewriting.
    if (← isClass? type).isSome then
      if let some inst ← synthInstance? type then
        mvarId.assign inst
        continue
    else
      dischargeSide mvarId
  return true

/-- The core of the `grw` implementation. -/
partial def grewriteCore (relName : Name) (rel? : Option Expr) (e : Expr) (inv : Bool)
    (config : Config) : GRewriteM (Option (Expr × Expr)) :=
  withTraceNodeBefore `Meta.grewrite (fun _ ↦ return m!"visiting `{e}` in the \
    {if inv then "RHS" else "LHS"} of relation `{rel?.elim m!"→" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, inv)
  if (← get).cache.contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return none
  let (mvar, goal) ← makeGCongrGoal rel? e inv
  -- Try the given grewrite lemma.
  let lem ← read
  if (e.toHeadIndex, e.headNumArgs) == lem.index then
    if ← lem.apply goal.mvarId! (inv != lem.symm) config then
      modify ({ · with progress := .matched })
      return (mvar, goal)
  -- Try all applicable `@[gcongr]` lemmas.
  if let some (head, args) := getCongrAppFnArgs e then
    let key := { relName, head, arity := args.size }
    let lemmas := ((gcongrExt.getState (← getEnv)).get? key).getD (relImpRelLemma args.size)
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if gcongrLem.forGrw then
        if ← processGCongrLemma goal.mvarId! gcongrLem inv config then
          return (← instantiateMVars mvar, goal)
        setMCtx mctx
  -- Cache the fact that there was nothing to rewrite.
  modify fun s ↦ { s with cache := s.cache.insert cacheKey }
  return none

end

end singlePass

/--
Rewrite `e` using the relation `hrel : x ~ y`, and construct an implication proof
using the `gcongr` tactic to discharge this goal.

if `forwardImp = true`, we prove that `e → eNew`; otherwise `eNew → e`.

If `symm = false`, we rewrite `e` to `eNew := e[x/y]`; otherwise `eNew := e[y/x]`.

The code aligns with `Lean.MVarId.rewrite` as much as possible.
-/
public def _root_.Lean.MVarId.grewrite (goal : MVarId) (e : Expr) (hrel : Expr)
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
        grewriteUsingKAbstract goal e hrel pattern replacement forwardImp config
      else
      withReducible do
      let some (_, lhs', rhs') := GCongr.getRel (← whnf hrelType) |
        throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
      -- Support relations that flip their arguments when reduced, such as `≥`.
      let symm' ←
        if lhs' == lhs && rhs' == rhs then pure symm
        else if lhs' == rhs && rhs' == lhs then pure !symm
        else throwTacticEx `grewrite goal m!"{hrelType} is not a valid relation"
      let index := (pattern.toHeadIndex, pattern.headNumArgs)
      let mvarIds := mvarIds ++ newMVars.map (·.mvarId!, #[])
      if let (some (eNew, impProof), newGoals) ←
        grewriteCore `_Implies none e (!forwardImp) config |>.run
          { symm := symm', proof := hrel, type := hrelType, index, mvarIds }
          |>.run' {} |>.run then
        pure (eNew, impProof, newGoals)
      else
        withLocalDeclD `_ (← inferType replacement) fun replacement' ↦ do
          let hrelType := updateRel hrelType replacement' symm
          throwTacticEx `grewrite goal
            m!"Did not find a rewrite with{indentExpr hrelType}\n\
            in the target expression{indentExpr e}\n\n\
            Use the command `set_option trace.Meta.grewrite true` to inspect this."
    -- post-process the metavariables
    postprocessAppMVars `grewrite goal newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← (sideGoals ++ newMVars.map Expr.mvarId!).filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew, impProof, mvarIds := newMVarIds.toList }

end Mathlib.Tactic.GRewrite
