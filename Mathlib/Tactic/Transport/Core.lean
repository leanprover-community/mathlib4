/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Common

/-!
## haha
-/


-- TODO: version of `getRel` that checks that the relation is a transport relation.

@[expose]
public def FunctionRel {α β : Type*} {γ : β → Type*} {δ : α → Type*}
    (r : α → β → Prop) (r' : ∀ {a b}, γ b → δ a → Prop)
    (g : ∀ b, γ b) (f : ∀ a, δ a) : Prop :=
  ∀ {a b}, r a b → r' (g b) (f a)

meta section

open Mathlib Tactic GRewrite

open Lean Meta GCongr

initialize registerTraceClass `transport

namespace Test

inductive RelKind where
  | imp | eq | other
  deriving Inhabited, BEq, Ord

/-- `GCongrKey` is the key used in the dictionary for looking up `gcongr` lemmas. -/
structure TransportKey where
  /-- The kind of relation. -/
  relKind : RelKind
  /-- The name of the head function. For example, `a + b ≤ a + c` has ``head := `HAdd.hAdd``. -/
  head : HeadIndex
  /-- The number of arguments that `head` is applied to.
  For example, `a + b ≤ a + c` has `arity := 6`, because `HAdd.hAdd` has 6 arguments. -/
  arity : Nat
deriving Inhabited, BEq

-- TODO: this instance is horrible
instance : Ord TransportKey where
  compare a b := compare (hash a.2) (hash b.2) |>.then (compare a.1 b.1) |>.then (compare a.3 b.3)

/-- The data for a "main" hypothesis of a `transport` lemma.
That is a hypothesis of the form `∀ xs, a xs' ~ b xs'` where `xs'` is a subset of `xs`,
and `a` and `b` form a "varying pair" in the conclusion of the `gcongr` lemma. -/
structure TransportHyp where
  /-- Index of the left varying argument. -/
  lhsIdx : Nat
  /-- Index of the right varying argument. -/
  rhsIdx : Nat
  /-- Index of the hypothesis itself. -/
  hypIdx : Nat
  /--
  In `∀ xs, a xs' ~ b xs''`, for each `x` in `xs`, the position it appears in `xs'`/`xs''`,
  and whether it appears in both.
  This information is used to infer suitable names when introducing these variables. -/
  hypsPos : List (Option Nat)
  relHyps : List (Nat × Nat × Nat × Bool)
  /-- Whether the order of the two varying arguments is the opposite from in the conclusion. -/
  isContra : Bool

/-- Structure recording the data for a `@[transport]` lemma. -/
structure TransportLemma where
  /-- The keys under which the lemma is stored. This is usually one key,
  but for `gcongr strict` lemmas, this stores two keys, for the LHS and RHS respectively. -/
  keys : List TransportKey
  /-- The given priority of the lemma, for example as `@[transport high]`. -/
  prio : Nat
  /--
  Universe parameter names for universe polymorphic proofs.
  It is non-empty only when we elaborate an expression provided by the user.
  When `proof` is just a constant, we use the universe parameter names stored in the declaration.
  -/
  levelParams : Array Name := #[]
  proof       : Expr
  /-- The number of arguments that `declName` takes when applying it. -/
  numHyps : Nat
  /--
  All pairs of types `α`, `β` such that `α` translates to/from `β`.
  TODO: make this an `Array` instead of `Option`.
  -/
  relatedTypes : Option (Nat × Nat)
  /-- The variables that appear on both sides of the conclusion. -/
  sharedVars : List Nat
  /-- `mainSubgoals` are the subgoals on which `gcongr` will be recursively called. -/
  mainSubgoals : Array TransportHyp
  deriving Inhabited

def TransportLemma.getValue (lem : TransportLemma) : MetaM Expr := do
  if lem.proof.isConst && lem.levelParams.isEmpty then
    let info ← getConstVal lem.proof.constName!
    if info.levelParams.isEmpty then
      return lem.proof
    else
      return lem.proof.updateConst! (← info.levelParams.mapM fun _ => mkFreshLevelMVar)
  else
    let us ← lem.levelParams.mapM fun _ => mkFreshLevelMVar
    return lem.proof.instantiateLevelParamsArray lem.levelParams us

/-- A collection of `TransportLemma`, to be stored in the environment extension. -/
abbrev TransportLemmas := Std.TreeMap TransportKey (List TransportLemma)

/-- Return `true` if the priority of `a` is less than or equal to the priority of `b`. -/
def TransportLemma.prioLE (a b : TransportLemma) : Bool :=
  a.prio ≤ b.prio

/-- Insert a `TransportLemma` in a collection of lemmas, making sure they are sorted by priority. -/
def addTransportLemmaEntry (m : TransportLemmas) (l : TransportLemma) : TransportLemmas :=
  l.keys.foldl (init := m) fun m key ↦ m.alter key fun
    | none    => [l]
    | some es => insert l es
where
  /--- Insert a `TransportLemma` in the correct place in a list of lemmas. -/
  insert (l : TransportLemma) : List TransportLemma → List TransportLemma
    | []     => [l]
    | l'::ls => if l'.prioLE l then l::l'::ls else l' :: insert l ls

/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
initialize transportExt : SimpleScopedEnvExtension TransportLemma TransportLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := addTransportLemmaEntry
    initial := {}
  }


structure Context where
  /-- The function that determines how a type should be translated. -/
  translateType : Expr → MetaM Expr
  /--
  The collection of transport lemmas.
  This can include ones passed to the `transport` tactic by a user.
  -/
  lemmas : TransportLemmas
  /--
  A map from introduced free variables `a` to the proof of their relation `r a b` to its
  corresponding variable. The `Bool` is `true` in the case `r a b` and `false` in the case `r b a`.
  -/
  transportHyps : FVarIdMap (FVarId × Bool) := {}

abbrev TransportM := ReaderT Context GCongrM

def withTransportHyps {α} (hyps : List (FVarId × FVarId × Bool)) (goal : MVarId)
    (k : MVarId → TransportM α) : TransportM α := do
  match hyps with
  | [] => k goal
  | (fvarId, hRel, forward) :: hyps =>
    let rel ← instantiateMVars (← hRel.getType)
    if rel.isEq then
      let (_, goal) ← substCore goal hRel (symm := !forward)
      goal.withContext <| withTransportHyps hyps goal k
    else
      trace[transport] "`{Expr.fvar fvarId}` satisfies `{rel}`"
      withReader
        (fun c ↦ { c with transportHyps := c.transportHyps.insert fvarId (hRel, forward) })
        (withTransportHyps hyps goal k)

-- structure LCtx where
--   lctx : LocalContext
--   linsts : LocalInstances

-- def LCtx.add (l : LCtx) (fvarId : FVarId) : MetaM LCtx := do
--   let decl ← fvarId.getDecl
--   return {
--     lctx := l.lctx.addDecl decl
--     linsts :=
--       if let some className := ← isClass? decl.type then
--         l.linsts.push { fvar := .fvar fvarId, className }
--       else
--         l.linsts
--   }
-- #check LocalContext.addDecl
-- #check withLocalDecl
/-- Apply generalized congruence lemma `lem` to goal `g`, throwing an error if it fails.
Return an array of main subgoals and an array of side goals.
For each main subgoal, also return whether the sides of the relation are swapped
(i.e. whether it is contravariant).

This function is used by both the `gcongr` and `grw` tactic.
In the case of `grw`, one of the two sides of the goal is a metavariable that is filled in
by this function.

In the main subgoals, the forall binders are introduced. They are named using the `with` clause of
`gcongr`, or otherwise using binder names in the goal. `grw` relies on these names to ensure that
binder names are preserved in the goal.
-/
def applyGCongrLemma (g : MVarId) (lem : TransportLemma) :
    TransportM
      (Array (MVarId × List (FVarId × FVarId × FVarId × Bool) × Bool) × Array MVarId) := do
  let proof ← lem.getValue
  let type ← inferType proof
  let (mvars, bis, type) ← forallMetaBoundedTelescope type lem.numHyps
  guard <| ← approxDefEq <| isDefEq (← g.getType) type
  -- Check that no transport variables accidentally end up in the result.
  for i in lem.sharedVars do
    let transportVars := (← read).transportHyps
    if (← instantiateMVars mvars[i]!).hasAnyFVar transportVars.contains then
      throwError "`{mvars[i]!}` contains a variable that it shouldn't"
  if let some (i, j) := lem.relatedTypes then
    let α ← instantiateMVars mvars[i]!
    let β ← instantiateMVars mvars[j]!
    let setType (oldType mvar : Expr) := do
      let newType ← (← read).translateType oldType
      unless ← isDefEq newType mvar do throwError "failed to assing {mvar} with `{newType}`"
    match α.isMVar, β.isMVar with
    | false, true => setType α β
    | true, false => setType β α
    | _, _ => throwError "expected exactly one of `{α}` and `{β}` to be a metavariable"
  g.assign (mkAppN proof mvars)
  let mut sideGoals := #[]
  for mvar in mvars, i in 0...* do
    let mvarId := mvar.mvarId!
    if ← mvarId.isAssigned then continue
    -- Filter out metavariables from the main subgoals
    if lem.mainSubgoals.any (fun h ↦ h.lhsIdx == i || h.rhsIdx == i || h.hypIdx == i) then continue
    -- Synthesize instance implicit arguments.
    -- We allow synthesis to get stuck, because in the case of `grw`
    -- there may be unassigned metavariables in the type.
    if bis[i]!.isInstImplicit then
      match ← trySynthInstance (← mvarId.getType) with
      | .some inst => mvarId.assign inst; continue
      | .none => failure
      | .undef => sideGoals := sideGoals.push mvarId
    else
      sideGoals := sideGoals.push mvarId
  let mainGoals ← lem.mainSubgoals.mapM fun h ↦ do
    let mvarId := mvars[h.hypIdx]!.mvarId!
    -- Use binder names appearing in the LHS/RHS of the target relation.
    let lhsNames := lambdaBinderNames (← instantiateMVars mvars[h.lhsIdx]!)
    let rhsNames := lambdaBinderNames (← instantiateMVars mvars[h.rhsIdx]!)
    let lambdaNames := if lhsNames.size ≥ rhsNames.size then lhsNames else rhsNames
    let names := h.hypsPos.map (·.elim `_ (lambdaNames.getD · `_))
    let (fvarIds, mvarId) ← mvarId.introN h.hypsPos.length names
    let relHyps := h.relHyps.map fun (i, j, k, b) ↦ (fvarIds[i]!, fvarIds[j]!, fvarIds[k]!, b)
    return (mvarId, relHyps, h.isContra)
  return (mainGoals, sideGoals)
where
  /-- Get the binder names from a lambda function. -/
  lambdaBinderNames (e : Expr) (acc : Array Name := #[]) : Array Name :=
    match e with
    | .lam n _ b _ => lambdaBinderNames b (acc.push n)
    | _ => acc

/-- Get the `gcongr` lemmas whose conclusion has the shape
`relName (head ..) _`, if `forward := true`, or `rel _ (head ..)`, if `forward := false`.
`arity` is the number of arguments in `..`. This is used by the `grw` tactic. -/
def findTransportLemmas? (relKind : RelKind) (head : HeadIndex) (forward : Bool) (arity : Nat) :
    TransportM (List TransportLemma) := do
  let some lemmas := (← read).lemmas.get? { relKind, head, arity } | return []
  if forward then
    return lemmas.filter (·.keys.head!.head == head)
  else
    return lemmas.filter (·.keys.getLast!.head == head)

/-- If `e` is of the form `r a b`, return `(r, a, b)`.
Note: we assume that `e` does not have an `Expr.mdata` annotation. -/
def getRel (e : Expr) : MetaM (Option (RelKind × CollectFVars.State × Expr × Expr)) := do
  match e with
  | mkApp3 (.const ``Eq _) ty lhs rhs => return some (.eq, collectFVars {} ty, lhs, rhs)
  | mkApp2 r lhs rhs => return some (.other, collectFVars {} r, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      let fvars := collectFVars (collectFVars {} (← inferType lhs)) (← inferType rhs)
      return some (.imp, fvars, lhs, rhs)
    else
      return none
  | _ => return none

/-- Version of `getRel` that also returns the expression of the relation. -/
def getRel' (e : Expr) : Option (RelKind × Option Expr × Expr × Expr) :=
  match e with
  | mkApp2 rel@(.app (.const ``Eq _) _) lhs rhs => some (.eq, rel, lhs, rhs)
  | mkApp2 rel lhs rhs => some (.other, rel, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (.imp, none, lhs, rhs)
    else
      none
  | _ => none

-- TODO: `eta` reduce in lemmas.

/-- Try to construct the `TransportLemma` for a lemma with hypotheses `hyps` and
conclusion `target`. -/
def mkTransportLemmaCore (hyps : Array Expr) (target : Expr) (proof : Expr)
    (levelParams : Array Name) (prio : Nat) : MetaM TransportLemma := do
  let some (relKind, sharedVars, lhs, rhs) ← getRel target | throwError "No relation found"
  let hyps := hyps.map (·.fvarId!)
  if let .fvar fvarId := lhs.getAppFn then
    if hyps.contains fvarId then
      throwError "LHS is a variable: {lhs}"
  if let .fvar fvarId := rhs.getAppFn then
    if hyps.contains fvarId then
      throwError "RHS is a variable: {rhs}"
  let mut mainSubgoals := #[]
  let sharedVars := (← sharedVars.addDependencies).fvarSet.filter hyps.contains
  let lctx ← getLCtx
  let lhsVars :=
    (← (collectFVars {} lhs).addDependencies).fvarSet.filter fun fvarId ↦
      hyps.contains fvarId && !sharedVars.contains fvarId
        && !(lctx.get! fvarId).binderInfo.isInstImplicit
  let rhsVars :=
    (← (collectFVars {} rhs).addDependencies).fvarSet.filter fun fvarId ↦
      hyps.contains fvarId && !sharedVars.contains fvarId
        && !(lctx.get! fvarId).binderInfo.isInstImplicit
  let overlapping := lhsVars.inter rhsVars
  let lhsVars := lhsVars.diff overlapping
  let rhsVars := rhsVars.diff overlapping
  let lVarsRef ← IO.mkRef lhsVars
  let rVarsRef ← IO.mkRef rhsVars
  -- iterate over antecedents `hyp` to the lemma
  for hyp in hyps, i in 0...* do
    unless ← isProp (← hyp.getType) do
      continue
    -- Checks if `∀ xs, lhs ~ rhs` is a valid "main goal".
    let isMainGoal? (lhs rhs : Expr) (xs : Array Expr) : MetaM (Option TransportHyp) :=
      lhs.withApp fun lhs lhsArgs => rhs.withApp fun rhs rhsArgs => do
      /-
      The relation needs to be of the form `lhs y₁ ... yₙ ~ rhs z₁ ... zₙ`,
      where `yᵢ` and `zᵢ` are free variables from `xs`,
      and `lhs`, `rhs` are variables from the two sides of the conclusion of the lemma.
      If `yᵢ` is different from `zᵢ`, then they need to be related by a hypothesis `xⱼ : r yᵢ zᵢ`.
      -/
      let .fvar lhs := lhs | return none
      let .fvar rhs := rhs | return none
      if h : lhsArgs.size ≠ rhsArgs.size then
        return none
      else
      let mut hypsPos : Vector (Option Nat) xs.size := .replicate _ none
      let mut pairs : Std.HashMap (Expr × Expr) (Nat × Nat) := {}
      for h : i in *...lhsArgs.size do
        let lhsArg := lhsArgs[i]'h
        let rhsArg := rhsArgs[i]
        if lhsArg == rhsArg then
          let some idx := xs.finIdxOf? lhsArg | return none
          if (hypsPos[idx]'idx.2).isSome then
            return none
          hypsPos := hypsPos.set idx (some i) idx.2
        else
          let some idxL := xs.finIdxOf? lhsArg | return none
          if (hypsPos[idxL]'idxL.2).isSome then
            return none
          hypsPos := hypsPos.set idxL (some i) idxL.2
          let some idxR := xs.finIdxOf? rhsArg | return none
          if (hypsPos[idxR]'idxR.2).isSome then
            return none
          hypsPos := hypsPos.set idxR (some i) idxR.2
          pairs := pairs.insert (lhsArg, rhsArg) (idxL, idxR)
      let mut relHyps := #[]
      for h : i in *...xs.size do
        if let mkApp2 rel l r ← inferType (xs[i]'h) then
          if l.isFVar && r.isFVar then
            let fvarIds := (collectFVars {} rel).fvarIds
            unless fvarIds.any (fun f ↦ lhsVars.contains f || rhsVars.contains f) do
              if let some (idxL, idxR) := pairs[(l, r)]? then
                pairs := pairs.erase (l, r)
                relHyps := relHyps.push (idxL, idxR, i, true)
              else if let some (idxR, idxL) := pairs[(r, l)]? then
                pairs := pairs.erase (r, l)
                relHyps := relHyps.push (idxR, idxL, i, false)
      unless pairs.isEmpty do
        return none
      let some lhsIdx := hyps.idxOf? lhs | return none
      let some rhsIdx := hyps.idxOf? rhs | return none
      let lVars ← lVarsRef.get
      let rVars ← rVarsRef.get
      let isContra ←
        if lVars.contains lhs && rVars.contains rhs then
          lVarsRef.modify (·.erase lhs)
          rVarsRef.modify (·.erase rhs)
          pure false
        else
          if lVars.contains rhs && rVars.contains lhs then
            lVarsRef.modify (·.erase rhs)
            rVarsRef.modify (·.erase lhs)
            pure true
          else
            return none
      return some {
        lhsIdx
        rhsIdx
        hypIdx := i
        hypsPos := hypsPos.toList
        relHyps := relHyps.toList
        isContra
      }
    -- Checks if `hyp` is a valid "main goal".
    let go := forallTelescope (← hyp.getType) fun xs hypTy => do
      if let mkApp2 _ lhs₁ rhs₁ := hypTy then
        isMainGoal? lhs₁ rhs₁ xs
      else if let some lastFVar := xs.back? then
        isMainGoal? (← inferType lastFVar) hypTy xs.pop
      else
        return none
    if let some mainSubgoal ← go then
      mainSubgoals := mainSubgoals.push mainSubgoal
  let lVars ← lVarsRef.get
  let rVars ← rVarsRef.get
  let mut relatedTypes := none
  if let [α] := lVars.toList then
    if let [β] := rVars.toList then
      if (← inferType (← α.getType)) matches .sort (.succ _) then
        if (← inferType (← β.getType)) matches .sort (.succ _) then
          relatedTypes := some (hyps.idxOf α, hyps.idxOf β)
  if relatedTypes.isNone && (!lVars.isEmpty || !rVars.isEmpty) then
    logWarning m!"Could not find a subgoal relating \
      `{lVars.toList.map Expr.fvar}` and `{rVars.toList.map Expr.fvar}`"
  let mut keys := [{ relKind, head := rhs.toHeadIndex, arity := rhs.headNumArgs }]
  if rhs.toHeadIndex != lhs.toHeadIndex || rhs.headNumArgs != lhs.headNumArgs then
    keys := { relKind, head := lhs.toHeadIndex, arity := lhs.headNumArgs } :: keys
  return {
    keys, prio
    levelParams, proof
    numHyps := hyps.size
    relatedTypes
    sharedVars := sharedVars.toList.map hyps.idxOf
    mainSubgoals
  }

def mkTransportLemma (type proof : Expr) (levelParams : Array Name) (prio : Nat) :
    MetaM TransportLemma := do
  forallTelescope type fun xs type => do
  -- If the conclusion is a free variable, it is a lemma like `imp_imp_imp` or `forall_imp`,
  -- so we revert the last two variables.
  if type matches .fvar _ | .app (.fvar _) _ then
    let type ← mkForallFVars xs[(xs.size-2)...xs.size] type
    return ← mkTransportLemmaCore xs.pop.pop type proof levelParams prio
  try
    -- Add a `transport` lemma in the "normal" way.
    mkTransportLemmaCore xs type proof levelParams prio
  catch e => try
    let some x := xs.back? | failure
    let type ← mkForallFVars #[x] type
    mkTransportLemmaCore xs.pop type proof levelParams prio
  catch _ =>
    -- If none of the methods work, we throw the error thrown by the "normal" attempt.
    throw e

def mkTransportLemmaFromConst (declName : Name) (prio : Nat) : MetaM TransportLemma := do
  let cinfo ← getConstInfo declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  mkTransportLemma cinfo.type val #[] prio

def mkTransportLemmaFromExpr (proof : Expr) (levelParams : Array Name)
    (prio : Nat := eval_prio high) : MetaM TransportLemma := do
  if proof.isConst then
    mkTransportLemmaFromConst proof.constName! prio
  else
    mkTransportLemma (← inferType proof) proof levelParams prio

def elabTransportTheorem (stx : Syntax) : Elab.TermElabM TransportLemma :=
  withReducible <| withRef stx do
  let (levelParams, proof) ← Elab.Term.withoutModifyingElabMetaStateWithInfo <| withRef stx do
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return (r.paramNames, r.expr)
    else
      return (#[], e)
  mkTransportLemmaFromExpr proof levelParams

/-- Attribute marking transport lemmas. -/
syntax (name := transportAttr) "transport" (ppSpace prio)? : attr

/-- Mark `declName` with the `transport` attribute. -/
def addTransportLemma (declName : Name) (stx : Syntax) (kind : AttributeKind) : MetaM Unit :=
  withReducible do
  let prio ← getAttrParamOptPrio stx[1]
  let lem ← mkTransportLemmaFromConst declName prio
  transportExt.add lem kind

@[inherit_doc transportAttr]
initialize registerBuiltinAttribute {
  name := `transportAttr
  descr := "transport"
  add := (addTransportLemma · · · |>.run')
}





/-- The result returned by `Lean.MVarId.grewrite`. -/
public structure GRewriteResult where
  /-- The rewritten expression -/
  eNew : Expr
  /-- The proof of the implication. The direction depends on the argument `forwardImp`. -/
  impProof : Expr
  /-- The new side goals -/
  mvarIds : List MVarId -- new goals


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


mutual

/-- Recursively call `transportCore` to process a subgoal of a `gcongr` lemma.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processTransportHypothesis (goal : MVarId)
    (relHyps : List (FVarId × FVarId × FVarId × Bool))
    (forward fail : Bool) : TransportM Bool := do
  goal.withContext do
  let relHyps :=
    if forward then relHyps.map fun (i, _, k, b) ↦ (i, k, b)
    else relHyps.map fun (_, j, k, b) ↦ (j, k, !b)
  withTransportHyps relHyps goal fun goal ↦ do
  let some (relName, rel?, lhs, rhs) := getRel' (← goal.getType) |
    throwError "internal `grewrite` error: invalid `gcongr` goal {goal}"
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  let target ← instantiateMVars target; let rel? ← rel?.mapM instantiateMVars
  let some (result, proof) ← transportCoreOrRfl relName rel? target forward |
    if fail then
      throwError "transport made no progress on `{target}`"
    return false
  -- Assign any remaining universe variables
  unless ← isDefEq (← inferType mvarApp) (← inferType result) do
    throwError "internal `transport` error: couldn't set `{mvarApp}` to `{result}`"
  mvarApp.withApp fun mvar xs ↦ do
    /- Note: the names of the free variables `xs` end up in the new goal as lambda binders.
    `applyGCongrLemma` ensures that these are the binder names that appear in the original goal.
    As a result, when rewriting inside of `{x | p x}`, the binder name `x` is preserved. -/
    mvar.mvarId!.assign (← mkLambdaFVars xs result)
  goal.assign proof
  return true

/-- Apply the `gcongr` lemma to the goal. The main subgoals are visited for rewriting in,
and otherwise closed `by rfl`. If at least one rewrite has happened, we commit to this lemma,
and we try to discharge the side goals.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processGCongrLemma (e : Expr) (rel? : Option Expr) (lem : TransportLemma)
    (forward : Bool) : TransportM (Option (Expr × Expr)) :=
  withTraceNode `transport (fun _ ↦
    return m!"applying transport lemma `{lem.proof}`") do
  let (mvar, goal) ← makeGCongrGoal rel? e forward
  let (mainGoals, sideGoals) ←
    try
      applyGCongrLemma goal.mvarId! lem
    catch e =>
      trace[transport] "{e.toMessageData}"
      return none
  -- Recursively rewrite in the main subgoals
  for (goal, relHyps, isContra) in mainGoals do
    unless ← processTransportHypothesis goal relHyps (forward != isContra) rel?.isNone do
      return none
  let result ← instantiateMVars mvar
  if result == e then
    return none
  -- Finally, run the discharger on the side goals.
  for mvarId in sideGoals do
    let type ← mvarId.getType
    -- There may be instance side goals that still had metavariables before recursively rewriting.
    if (← isClass? type).isSome then
      if let .some inst ← trySynthInstance type then
        mvarId.assign inst
        continue
    else
      dischargeSide mvarId
  trace[transport] "result: {result}"
  return (result, goal)

partial def useTransportHyp (hyp : Expr) (goal : MVarId) (forward : Bool) : TransportM Bool := do
  let type := (← instantiateMVars (← inferType hyp)).headBeta
  if type.isAppOfArity ``FunctionRel 8 then
    let (mvars, _, _) ← withDefault <| forallMetaTelescopeReducing type (some 3)
    if ← useTransportHyp (mkAppN hyp mvars) goal forward then
      let some (relKind, rel?, lhs, rhs) := getRel' (← instantiateMVars (← inferType mvars[2]!))
        | return false
      let e ← instantiateMVars <| if forward then rhs else lhs
      let some (result, proof) ← transportCoreOrRfl relKind rel? e forward
        | return false
      let mvar := if forward then lhs else rhs
      unless ← isDefEq (← inferType result) (← inferType mvar) do
        return false
      mvar.mvarId!.assign result
      mvars[2]!.mvarId!.assign proof
      return true
  if ← isDefEq (← goal.getType) type then
    goal.assign hyp
    return true
  return false

/-- The core of the `grw` implementation. Rewrite in the expression `e` which occurs under the
relation `relName`/`rel?`, using the `GRewriteLemma` stored in `MetaM`.
If `e` itself cannot be rewritten, descend into subexpressions of `e` using `@[gcongr]` lemmas.

`rel?` should be an expression with head symbol `relName`,
unless the relation is `→`: `relName` is `_Implies` and `rel?` is `none`.

Returns the new expression and a proof that it is related to `e`, if a rewrite was found. -/
partial def transportCore (relKind : RelKind) (rel? : Option Expr) (e : Expr) (forward : Bool)
    (inSimp := false) :
    TransportM (Option (Expr × Expr)) := do
  if !inSimp && relKind matches .eq then
    if forward then
      transportEqCore e
    else
      (← transportEqCore e).mapM fun (e', pf) ↦ return (e', ← mkAppM ``Eq.symm #[pf])
  else withTraceNodeBefore `transport (fun _ ↦ return m!"visiting `{e}` in the \
    {if forward then "LHS" else "RHS"} of relation `{rel?.elim m!"→" (m!"{·}")}`") do
  let e := e.cleanupAnnotations
  if let .fvar fvarId := e.getAppFn then
    if let some (hyp, forward') := (← read).transportHyps.get? fvarId then
      let mctx ← getMCtx
      let (mvar, goal) ← makeGCongrGoal rel? e forward
      if let some goal' ←
        if forward != forward' then
          try some <$> goal.mvarId!.applySymm catch _ => pure none
        else
          pure <| some goal.mvarId! then
        if ← useTransportHyp (.fvar hyp) goal' forward' then
          trace[transport] "rewriting `{e}` to `{mvar}`"
          return some (← instantiateMVars mvar, goal)
      setMCtx mctx
  -- Try all applicable `@[transport]` lemmas.
  let lemmas ← findTransportLemmas? relKind e.toHeadIndex forward e.headNumArgs
  let mctx ← getMCtx
  for gcongrLem in lemmas do
    if let some (result, proof) ← processGCongrLemma e rel? gcongrLem forward then
      -- Preserve the binder name/info in a forall.
      match e, result with
      | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, proof)
      | _, _ => return some (result, proof)
    setMCtx mctx
  if relKind matches .eq then
    -- Use `Eq.symm`, and then try again to find an applicable lemma
    let lemmas ← findTransportLemmas? relKind e.toHeadIndex (!forward) e.headNumArgs
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if let some (result, proof) ← processGCongrLemma e rel? gcongrLem (!forward) then
          let proof ← mkAppM ``Eq.symm #[proof]
          -- Preserve the binder name/info in a forall.
          match e, result with
          | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, proof)
          | _, _ => return some (result, proof)
      setMCtx mctx
  if relKind matches .imp then
    if let some (e', pf) ← transportEqCore e then
      return some (e', ← mkAppM (if forward then ``Eq.mp else ``Eq.mpr) #[pf])
  return none

partial def transportEqCore (e : Expr) : TransportM (Option (Expr × Expr)) := fun c c' s ↦ do
  let methods := { pre e := do
    unless e.isApp || e.isForall || e.isFVar do return .continue
    -- TODO: avoid running `inferType` on each visited expression.
    let α ← inferType e
    let some (e', pf) ←
        transportCore .eq (Expr.app (.const `Eq [← getLevel α]) α) e true true c c' s |
      return .continue
    return .done { expr := e', proof? := pf }
    }
  let (r, _) ← Simp.main e (← Simp.mkContext Simp.neutralConfig) (methods := methods)
  let transportVars := c.transportHyps
  if r.expr.hasAnyFVar transportVars.contains then
    return none
  return r.proof?.map (r.expr, ·)

partial def transportCoreOrRfl (relKind : RelKind) (rel? : Option Expr) (e : Expr)
    (forward : Bool) :
    TransportM (Option (Expr × Expr)) := do
  if let some result ← transportCore relKind rel? e forward then
    return result
  let transportVars := (← read).transportHyps
  if e.hasAnyFVar transportVars.contains then
    return none
  match relKind with
  | .eq => return some (e, ← mkAppM ``Eq.refl #[e])
  | .imp => return some (e, .lam `_ e (.bvar 0) .default)
  | .other =>
    let mvar := (← mkFreshExprMVar (mkApp2 rel?.get! e e))
    try
      -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
      withReducibleAndInstances mvar.mvarId!.applyRfl
      return some (e, ← instantiateMVars mvar)
    catch _ =>
      return none

end

open Elab Tactic

partial def translateDefault (k : Expr → MetaM (Option Expr)) (type : Expr) : MetaM Expr := do
  if let some type' ← k type then
    return type'
  if let .forallE n d b bi := type then
    if b.hasLooseBVars then
      withLocalDecl n bi d fun var ↦ do←
        return .forallE n d ((← translateDefault k (b.instantiate1 var)).abstract #[var]) bi
    else
      return .forallE n (← translateDefault k d) (← translateDefault k b) bi
  match_expr type with
  | f@Option α => return .app f (← translateDefault k α)
  | f@Set α => return .app f (← translateDefault k α)
  | f@Prod α β => return mkApp2 f (← translateDefault k α) (← translateDefault k β)
  | _ => return type

def translateGiven (translations : Array (Expr × Expr)) (type : Expr) : MetaM (Option Expr) := do
  for (before, after) in translations do
    if ← withoutModifyingMCtx (isDefEqI type before) then
      return after
  return none

public syntax transportClause := term "to" term

syntax "transport" (" [" term,* "]")? transportClause,* (" generalizing" (ppSpace colGt ident)*)?
  : tactic

elab_rules : tactic
| `(tactic| transport $[[$[$terms],*]]? $clauses:transportClause,* $[generalizing $xs*]?) => do
  let mvarId ← getMainGoal
  let tag ← mvarId.getTag
  let (mvarId, intros) ← mvarId.withContext do
    let fvarIds ← (xs.getD #[]).mapM (getFVarId ·.raw)
    let fvarIds ← sortFVarIds fvarIds
    let (fvarIds, mvarId) ← mvarId.revert fvarIds (preserveOrder := true)
    pure (mvarId, fvarIds.size)
  mvarId.withContext do
  let translations ← clauses.getElems.mapM fun ⟨stx⟩ ↦
    return (← elabTerm stx[0] none, ← elabTerm stx[2] none)
  let translateType := translateDefault (translateGiven translations)
  let givenLemmas ← (terms.getD #[]).mapM (elabTransportTheorem ·)
  let lemmas := transportExt.getState (← getEnv)
  let lemmas := givenLemmas.foldl addTransportLemmaEntry lemmas
  let type ← instantiateMVars (← mvarId.getType)
  let (some (e, pf), s) ← withReducible <|
    transportCore .imp none type false |>.run { translateType, lemmas } |>.run
    | throwError "transport made no progress on `{type}`"
  let newGoal ← mkFreshExprMVar e .syntheticOpaque
  mvarId.assign (pf.app newGoal)
  let (_, newGoal) ← newGoal.mvarId!.introNP intros
  newGoal.setTag tag
  replaceMainGoal (s.newGoals.toList ++ [newGoal])


end Test
