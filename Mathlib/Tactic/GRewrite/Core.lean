/-
Copyright (c) 2025 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
module

public meta import Lean.Meta.Tactic.Rewrite
public import Mathlib.Tactic.GCongr.Core

meta import Mathlib.Tactic.GCongr.Core

/-!
# The generalized rewriting tactic

This module defines the core of the `grw`/`grewrite` tactic.

This file provides two implementations of the tactic:
1. The simple implementation uses `kabstract` to determine where to rewrite,
   and then calls `MVarId.gcongr` to prove that the rewrite is valid.
   This is used by `nth_grw` and `grw +useKAbstract`.
2. The more sophisticated implementation has its own congruence loop, applying `gcongr` lemmas to
   create the replacement expression, and to prove that this is related to the original expression.
   This supports the use of strict inequalities to change the strictness in the goal.
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
  /-- The outermost local context in which the rewrite makes sense. If the rewrite does not involve
  bound variables, this is `none`. This is used for fixing the generated info tree, so that the
  "Expected Type" is displayed correctly. -/
  lctx? : Option LocalContext

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
  let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <|
    kabstract e pattern config.occs
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
  let (_, s) ← gcongrGoal.mvarId!.gcongr forwardImp
    |>.run (mainGoalDischarger := GRewrite.dischargeMain hrel)
  pure (eNew, gcongrGoal, s.newGoals)

end kabstract

section singlePass

initialize registerTraceClass `Meta.grewrite

/-- The congruence loop keeps track of its progress as follows.
- Each rewrite starts off as `.noMatch`.
- When a rewrite has first successfully been applied (with `applyGRewriteLemma`),
  this switches to `.matched lctx linsts maxFVar`,
  consisting of the current local context and local instances,
  and the last `gcongr` lemma variable that the rewrite depends on.
  This variable is used to determine in what local context it is valid to do more rewrites:
  if this variable is out of scope, then we can't do more rewrites.
- When another rewrite is successfully applied in a different local context,
  the `lctx` and `linsts` fields are set to the intersection of the different local contexts.
-/
inductive Progress where
  /-- The rewrite lemma has not unified with anything yet. -/
  | noMatch
  /-- The rewrite lemma has unified with something. -/
  | matched (lctx : LocalContext) (linsts : LocalInstances) (maxFVar : Option FVarId)

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
  mvarIds : Array (MVarId × Array LocalDecl × LocalInstances)
  /-- Number of indices in the starting local context. -/
  lctxInitIndices   : Nat := 0

/-- The monad used for `grw`. -/
abbrev GRewriteM := ReaderT GRewriteLemma StateRefT State GCongr.GCongrM

/-- Unify the given generalized rewrite lemma with the goal, so as to rewrite with it.
If `symm := true`, first use the `symm` tactic to swap the direction of the lemma.
`gcongr_forward` is used to deal with the case where the lemma is `a < b` and the goal is `a ≤ b`.
Returns whether the goal was closed by the lemma.
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
  -- `@[gcongr_forward]` extensions are metaprograms retrieved from `forwardExt`, so `shake` sees
  -- no reference to the module that registered them. We record that module below, for whichever
  -- extension closes the goal.
  for (n, tac) in (forwardExt.getState (← getEnv)).2 do
    -- Explicitly exclude a few `gcongr_forward` extensions that are not relevant here.
    if n matches ``GCongr.exact | ``GCongr.exactRefl then continue
    try
      tac.eval proof goal
      recordExtraModUseFromDecl (isMeta := true) n
      return true
    catch _ => setMCtx mctx
  return false

/--
Run `GRewriteLemma.apply`, ensuring that the metavariable context and `Progress` are set correctly.
-/
def applyGRewriteLemma (goal : MVarId) (symm : Bool) (config : GRewrite.Config) :
    GRewriteM Bool := do
  match (← get).progress with
  | .noMatch =>
    let lctx ← getLCtx
    let linsts ← getLocalInstances
    -- If no `gcongr` lemma variables were added to the local context,
    -- then we don't need to modify the metavariable context.
    if lctx.numIndices == (← read).lctxInitIndices then
      if ← (← read).apply goal symm config then
        modify ({ · with progress := .matched lctx linsts none})
        return true
      return false
    -- Update the local context of each metavariable to include the `gcongr` lemma variables.
    let mctx ← getMCtx
    setMCtx <| (← read).mvarIds.foldl (init := mctx) fun mctx (mvarId, decls, insts) ↦
      { mctx with
        decls := mctx.decls.insert mvarId {
          mctx.getDecl mvarId with
          lctx := decls.foldl (·.addDecl ·) lctx
          localInstances := linsts ++ insts } }
    if ← (← read).apply goal symm config then
      modify ({ · with progress := .matched lctx linsts (← getMaxFVar)})
      return true
    setMCtx mctx
    return false
  | .matched lctx linsts maxFVar =>
    if ← (← read).apply goal symm config then
      let mut lctx := lctx
      let mut linsts := linsts
      while let some lastDecl := lctx.lastDecl do
        if (← getLCtx).contains lastDecl.fvarId then break
        lctx := lctx.pop
        linsts := linsts.erase lastDecl.fvarId
      modify ({ · with progress := .matched lctx linsts maxFVar })
      return true
    return false
where
  /--
  If we have just successfully applied the grewrite lemma for the first time,
  then return the last `gcongr` variable that the rewrite depends on,
  i.e. the one with the highest `index`.
  This assumes that there is at least one introduced bound variable in the local context.
  -/
  getMaxFVar : GRewriteM (Option FVarId) := do
    let mvarIds := (← read).mvarIds
    let assignments ← mvarIds.filterMapM (getExprMVarAssignment? ·.1)
    -- If there is any unassigned metavariable, it can depend on any free variable,
    -- so we return the last free variable.
    if assignments.size < mvarIds.size then
      return (← getLCtx).lastDecl.map (·.fvarId)
    let usedFVars := (assignments.foldl Lean.collectFVars {}).fvarIds
    let mut maxFVar : Option (FVarId × Nat) := none
    for fvarId in usedFVars do
      let index := (← fvarId.getDecl).index
      if (← read).lctxInitIndices ≤ index then
        if maxFVar.all (·.2 < index) then
          maxFVar := (fvarId, index)
    return maxFVar.map (·.1)

/-- Create the `gcongr` goal corresponding to rewriting `e` by relation `rel?`,
so that we can apply `gcongr` lemmas to it. -/
def makeGCongrGoal (rel? : Option Expr) (e : Expr) (forward : Bool) : MetaM (Expr × Expr) := do
  if let some rel := rel? then
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
      let mvar ← mkFreshExprMVar d₂
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel e mvar)
    else
      let mvar ← mkFreshExprMVar d₁
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel mvar e)
  else
    let mvar ← mkFreshTypeMVar
    let target := if forward then .forallE `_a e mvar .default else .forallE `_a mvar e .default
    return (mvar, ← mkFreshExprMVar (some target))

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

/-- Recursively call `grewriteCore` to process a subgoal of a `gcongr` lemma.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processGCongrHypothesis (goal : MVarId) (forward : Bool) (config : Config) :
    GRewriteM Bool := goal.withContext do
  let some (relName, rel?, lhs, rhs) := getRel' (← whnf (← goal.getType)) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  if let some (result, proof) ← grewriteCore relName rel? target forward config then
    mvarApp.withApp fun mvar xs ↦ do
      /- Note: the names of the free variables `xs` end up in the new goal as lambda binders.
      `applyGCongrLemma` ensures that these are the binder names that appear in the original goal.
      As a result, when rewriting inside of `{x | p x}`, the binder name `x` is preserved. -/
      mvar.mvarId!.assign (← mkLambdaFVars xs result)
      goal.assign proof
      return true
  else
    return false

/-- Apply the `gcongr` lemma to the goal. The main subgoals are visited for rewriting in,
and otherwise closed `by rfl`. If at least one rewrite has happened, we commit to this lemma,
and we try to discharge the side goals.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processGCongrLemma (goal : MVarId) (lem : GCongrLemma) (forward : Bool)
    (config : Config) : GRewriteM Bool :=
  withTraceNode `Meta.grewrite (fun _ ↦
    return m!"applying `gcongr` lemma `{.ofConstName lem.declName}`") do
  let (mainGoals, sideGoals) ← try applyGCongrLemma goal lem catch _ => return false
  -- Recursively rewrite in the main subgoals
  let mut anyProgress := false
  for (goal, isContra) in mainGoals do
    if ← processGCongrHypothesis goal (forward != isContra) config then
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

/-- The core of the `grw` implementation. Rewrite in the expression `e` which occurs under the
relation `relName`/`rel?`, using the `GRewriteLemma` stored in `GRewriteM`.
If `e` itself cannot be rewritten, descend into subexpressions of `e` using `@[gcongr]` lemmas.

`rel?` should be an expression with head symbol `relName`,
unless the relation is `→`: `relName` is `_Implies` and `rel?` is `none`.

Returns the new expression and a proof that it is related to `e`, if a rewrite was found. -/
partial def grewriteCore (relName : Name) (rel? : Option Expr) (e : Expr) (forward : Bool)
    (config : Config) : GRewriteM (Option (Expr × Expr)) := do
  if let .matched _ _ (some fvarId) := (← get).progress then
    unless (← getLCtx).contains fvarId do
      return none
  withTraceNodeBefore `Meta.grewrite (fun _ ↦ return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"→" (m!"{·}")}`") do
  let e ← instantiateMVars e; let rel? ← rel?.mapM instantiateMVars
  let cacheKey := (rel?, e, forward)
  if (← get).cache.contains cacheKey then
    trace[Meta.grewrite] "cached: no rewrite"
    return none
  let (mvar, goal) ← makeGCongrGoal rel? e forward
  -- Try the given grewrite lemma.
  let lem ← read
  if (e.toHeadIndex, e.headNumArgs) == lem.index then
    if ← applyGRewriteLemma goal.mvarId! (forward == lem.symm) config then
      return (mvar, goal)
  -- Try all applicable `@[gcongr]` lemmas.
  if let some (head, args) := getCongrAppFnArgs e then
    let mut lemmas ← findGCongrLemmas?' relName head forward args.size
    if relName == `_Implies then
      lemmas := lemmas ++ relImpRelLemma args.size
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if gcongrLem.forGrw then
        if ← processGCongrLemma goal.mvarId! gcongrLem forward config then
          -- Preserve the binder name/info in a forall.
          match e, ← instantiateMVars mvar with
          | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, goal)
          | _, result => return some (result, goal)
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
    (mvarIds : Array (MVarId × Array LocalDecl × LocalInstances)) (forwardImp symm : Bool)
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
      return { eNew, impProof, mvarIds, lctx? := none }

    let hrelIn := hrel
    -- check that `hrel` proves a relation
    let hrel := mkAppN hrel newMVars
    let some (_, lhs, rhs) := GCongr.getRel hrelType |
      throwTacticEx `grewrite goal m!"`{hrelType}` is not a relation"
    let (pattern, replacement) := if symm then (rhs, lhs) else (lhs, rhs)
    if pattern.getAppFn.isMVar then
      throwTacticEx `grewrite goal
        m!"pattern is a metavariable{indentExpr pattern}\nfrom relation{indentExpr hrelType}"
    -- abstract the occurrences of `lhs` from `e` to get `eAbst`
    let e ← instantiateMVars e
    let ((lctx, linsts), eNew, impProof, sideGoals) ←
      if config.useKAbstract then
        ((← getLCtx, ← getLocalInstances), ·)
          <$> grewriteUsingKAbstract goal e hrel pattern replacement forwardImp config
      else
      withReducible do
      let some (_, lhs', rhs') := GCongr.getRel (← whnf hrelType) |
        throwTacticEx `grewrite goal m!"`{hrelType}` is not a valid relation"
      -- Support relations that flip their arguments when reduced, such as `≥`.
      let symm' ←
        if lhs' == lhs && rhs' == rhs then pure symm
        else if lhs' == rhs && rhs' == lhs then pure !symm
        else throwTacticEx `grewrite goal m!"`{hrelType}` is not a valid relation"
      let index := (pattern.toHeadIndex, pattern.headNumArgs)
      let mvarIds := mvarIds ++ newMVars.map (·.mvarId!, #[], #[])
      let ctx := {
        symm := symm', proof := hrel, type := hrelType, index, mvarIds
        lctxInitIndices := (← getLCtx).numIndices }
      if let ((some (eNew, impProof), { progress, ..}), s) ←
        grewriteCore `_Implies none e (forward := forwardImp) config
          |>.run ctx |>.run {} |>.run then
        let lctx ← match progress with
          | .matched lctx linsts _ => pure (lctx, linsts)
          | _ => throwError "internal `grewrite` error: succeeded without a match"
        pure (lctx, eNew, impProof, s.newGoals)
      else
        withLocalDeclD `_ (← inferType replacement) fun replacement' ↦ do
          let hrelType := updateRel hrelType replacement' symm
          throwTacticEx `grewrite goal
            m!"Did not find a rewrite with{indentExpr hrelType}\n\
            in the target expression{indentExpr e}\n\n\
            Use the command `set_option trace.Meta.grewrite true` to inspect this."
    -- post-process the metavariables
    withLCtx lctx linsts do
      postprocessAppMVars `grewrite goal newMVars binderInfos
        (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← (sideGoals ++ newMVars.map Expr.mvarId!).filterM (not <$> ·.isAssigned)
    let otherMVarIds ← getMVarsNoDelayed hrelIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure {
      eNew, impProof
      mvarIds := newMVarIds.toList
      lctx? := if lctx.numIndices == (← getLCtx).numIndices then none else some lctx }

end Mathlib.Tactic.GRewrite
