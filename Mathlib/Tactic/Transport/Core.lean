/-
Copyright (c) 2026 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.Common

import all Lean.Meta.DiscrTree.Main

/-!
## haha
-/


-- TODO: version of `getRel` that checks that the relation is a transport relation.
namespace TransportTest

@[expose]
public def FunctionRel {α β : Type*} (r : α → β → Prop) {γ : β → Type*} {δ : α → Type*}
    (r' : ∀ {a b}, r a b → γ b → δ a → Prop) (g : ∀ b, γ b) (f : ∀ a, δ a) : Prop :=
  ∀ {a b} (h : r a b), r' h (g b) (f a)

@[expose] public def MapRel {α β : Type*} (map : α → β) (a : α) (b : β) : Prop := map a = b

end TransportTest

meta section

open Mathlib Tactic TransportTest

open Lean Meta GCongr

initialize registerTraceClass `transport

namespace Test

inductive Rel where
  | imp | eq | relation | other (e : Expr)

instance : ToMessageData Rel where
  toMessageData
    | .imp => m!"_ → _"
    | .eq => m!"_ = _"
    | .relation => m!"_ → _ → Prop"
    | .other rel => m!"{rel}"

inductive RelKind where
  | imp | eq | rel | other
  deriving Inhabited, BEq, Ord

def Rel.toKind : Rel → RelKind
  | .imp => .imp
  | .eq => .eq
  | .relation => .rel
  | .other _ => .other

/-- `GCongrKey` is the key used in the dictionary for looking up `gcongr` lemmas. -/
structure TransportKey where
  /-- The kind of relation. -/
  relKind : RelKind
  /-- `true` if the relation is used left-to-right. -/
  forward : Bool
  deriving Inhabited, BEq, Ord

/-- The data for a "main" hypothesis of a `transport` lemma.
That is a hypothesis of the form `∀ xs, a xs' ~ b xs'` where `xs'` is a subset of `xs`,
and `a` and `b` form a "varying pair" in the conclusion of the `gcongr` lemma. -/
structure TransportHyp where
  /-- Index of the left varying argument. Used only for preserving names of bound variables. -/
  lhsIdx : Nat
  /-- Index of the right varying argument. Used only for preserving names of bound variables. -/
  rhsIdx : Nat
  /-- Index of the hypothesis itself. -/
  hypIdx : Nat
  /--
  In `∀ xs, a xs' ~ b xs''`, for each `x` in `xs`, the position it appears in `xs'`/`xs''`,
  and whether it appears in both.
  This information is used to infer suitable names when introducing these variables. -/
  hypsPos : List (Option Nat)
  relHyps : List (Nat × Nat × Nat)

/-- Structure recording the data for a `@[transport]` lemma. -/
structure TransportLemma where
  /-- The keys under which the lemma is stored. This is usually one key,
  but for `gcongr strict` lemmas, this stores two keys, for the LHS and RHS respectively. -/
  keys : List (TransportKey × Array DiscrTree.Key)
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
  /-- The variables that appear on both sides of the conclusion. -/
  sharedVars : List Nat
  /-- `mainSubgoals` are the subgoals on which `gcongr` will be recursively called. -/
  mainSubgoals : Array TransportHyp
  deriving Inhabited

instance : BEq TransportLemma := ⟨(·.proof == ·.proof)⟩

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

/--
A collection of `TransportLemma`, to be stored in the environment extension.
This includes lemmas for transporting left to right and right to left.
-/
abbrev TransportLemmas := Std.TreeMap TransportKey (DiscrTree TransportLemma)

/-- Return `true` if the priority of `a` is less than or equal to the priority of `b`. -/
def TransportLemma.prioLE (a b : TransportLemma) : Bool :=
  a.prio ≤ b.prio

/-- Insert a `TransportLemma` in a collection of lemmas, making sure they are sorted by priority. -/
def addTransportLemmaEntry (m : TransportLemmas) (lem : TransportLemma) : TransportLemmas :=
  lem.keys.foldl (init := m) fun m (key, keys) ↦
    m.alter key (·.getD {} |>.insertKeyValue keys lem)

/-- Environment extension for "generalized congruence" (`gcongr`) lemmas. -/
initialize transportExt : SimpleScopedEnvExtension TransportLemma TransportLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := addTransportLemmaEntry
    initial := {}
  }


structure Context where
  /--
  The collection of transport lemmas.
  This can include ones passed to the `transport` tactic by a user.
  -/
  lemmas : TransportLemmas
  /--
  A map from introduced free variables `a` to the proof of their relation `r a b` to its
  corresponding variable. The `Bool` is `true` in the case `r a b` and `false` in the case `r b a`.
  -/
  transportHyps : FVarIdMap FVarId := {}

abbrev TransportM := ReaderT Context GCongrM

def withTransportHyps {α} (hyps : List (FVarId × FVarId)) (goal : MVarId)
    (k : MVarId → TransportM α) : TransportM α := do
  match hyps with
  | [] => k goal
  | (fvarId, hRel) :: hyps =>
    let rel ← instantiateMVars (← hRel.getType)
    if rel.isEq then
      if ← isProp (← goal.getType) then
        let (_, goal) ← substCore goal hRel
        return ← goal.withContext <| withTransportHyps hyps goal k
    trace[transport] "variable `{Expr.fvar fvarId}` satisfies transport relation `{rel}`"
    withReader
      (fun c ↦ { c with transportHyps := c.transportHyps.insert fvarId hRel })
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
def applyGCongrLemma (g : MVarId) (lem : TransportLemma) (forward : Bool) :
    TransportM (Array (MVarId × List (FVarId × FVarId)) × Array MVarId) := do
  let proof ← lem.getValue
  let type ← inferType proof
  let (mvars, bis, type) ← forallMetaBoundedTelescope type lem.numHyps
  unless ← approxDefEq <| isDefEq (← g.getType) type do
    throwError "failed to unify `{← g.getType}` with `{type}`"
  -- Check that no transport variables accidentally end up in the result.
  for i in lem.sharedVars do
    let transportVars := (← read).transportHyps
    if (← instantiateMVars mvars[i]!).hasAnyFVar transportVars.contains then
      throwError "`{mvars[i]!}` contains a variable that it shouldn't"
  g.assign (mkAppN proof mvars)
  let mut sideGoals := #[]
  for mvar in mvars, i in 0...* do
    let mvarId := mvar.mvarId!
    if ← mvarId.isAssigned then continue
    -- Filter out metavariables from the main subgoals
    if lem.mainSubgoals.any (·.hypIdx == i) then continue
    -- Synthesize instance implicit arguments.
    -- We allow synthesis to get stuck, because in the case of `grw`
    -- there may be unassigned metavariables in the type.
    if bis[i]!.isInstImplicit then
      match ← trySynthInstance (← mvarId.getType) with
      | .some inst => mvarId.assign inst
      | .none => discard <| throwFailedToSynthesize (← mvarId.getType)
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
    let relHyps := h.relHyps.map fun (i, j, k) ↦
      (if forward then fvarIds[i]! else fvarIds[j]!, fvarIds[k]!)
    return (mvarId, relHyps)
  return (mainGoals, sideGoals)
where
  /-- Get the binder names from a lambda function. -/
  lambdaBinderNames (e : Expr) (acc : Array Name := #[]) : Array Name :=
    match e with
    | .lam n _ b _ => lambdaBinderNames b (acc.push n)
    | _ => acc

def findTransportLemmas? (rel : Rel) (e : Expr) (forward : Bool) :
    TransportM (Array TransportLemma) := do
  let lemmas := (← read).lemmas
  let some t := lemmas.get? { forward, relKind := rel.toKind } | return #[]
  let candidates ← if let .other rel := rel then getRelMatch t rel e else t.getMatch e
  return candidates.reverse.insertionSort (·.prio > ·.prio)
where
  /-- Look up in a discrimination tree using both `rel` and `e`. -/
  getRelMatch (d : DiscrTree TransportLemma) (rel e : Expr) : MetaM (Array TransportLemma) :=
    withReducible do
      let mut result := #[]
      if let some c := d.root.find? .star then
        result ← DiscrTree.getMatchLoop #[e] c #[]
      let (k, args) ← DiscrTree.getMatchKeyArgs rel (root := true)
      unless k matches .star do
        result ← DiscrTree.getMatchRoot d k (#[e] ++ args) result
      return result

/-- If `e` is of the form `r a b`, return `(r, a, b)`.
Note: we assume that `e` does not have an `Expr.mdata` annotation. -/
def getRel (e : Expr) : MetaM (Option (Rel × CollectFVars.State × Expr × Expr)) := do
  match e with
  | mkApp3 (.const ``Eq _) ty lhs rhs => return some (.eq, collectFVars {} ty, lhs, rhs)
  | mkApp2 r lhs rhs => return some (.other r, collectFVars {} r, lhs, rhs)
  | .forallE _ lhs (.forallE _ rhs (.sort 0) _) _ => return some (.relation, {}, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      let fvars := collectFVars (collectFVars {} (← inferType lhs)) (← inferType rhs)
      return some (.imp, fvars, lhs, rhs)
    else
      return none
  | _ => return none

/-- Version of `getRel` that also returns the expression of the relation. -/
def getRel' (e : Expr) : Option (Rel × Expr × Expr) :=
  match e with
  | mkApp3 (.const ``Eq _) _ lhs rhs => some (.eq, lhs, rhs)
  | mkApp2 rel lhs rhs => some (.other rel, lhs, rhs)
  | .forallE _ lhs (.forallE _ rhs (.sort 0) _) _ => some (.relation, lhs, rhs)
  | .forallE _ lhs rhs _ =>
    if !rhs.hasLooseBVars then
      some (.imp, lhs, rhs)
    else
      none
  | _ => none

-- def mkTransportKey (hyps : Array FVarId) (rel : Rel) (e : Expr) (forward : Bool)

/-- Try to construct the `TransportLemma` for a lemma with hypotheses `hyps` and
conclusion `target`. -/
def mkTransportLemmaCore (hyps' : Array Expr) (target : Expr) (proof : Expr)
    (levelParams : Array Name) (dir : Option Bool) (prio : Nat) : MetaM TransportLemma := do
  let some (rel, sharedVars, lhs, rhs) ← getRel target
    | throwError "`{target}` is not a relation"
  trace[transport] "relating `{lhs}` to `{rhs}`"
  let hyps := hyps'.map (·.fvarId!)
  let sharedVars := (← sharedVars.addDependencies).fvarSet.filter hyps.contains
  if let .fvar fvarId := lhs.getAppFn then
    if hyps.contains fvarId && !sharedVars.contains fvarId then
      throwError "LHS is an arbitrary variable: `{lhs}`"
  if let .fvar fvarId := rhs.getAppFn then
    if hyps.contains fvarId && !sharedVars.contains fvarId then
      throwError "RHS is an arbitrary variable: `{rhs}`"
  let mut mainSubgoals := #[]
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
                relHyps := relHyps.push (idxL, idxR, i)
              else if let some (idxR, idxL) := pairs[(r, l)]? then
                pairs := pairs.erase (r, l)
                relHyps := relHyps.push (idxR, idxL, i)
      unless pairs.isEmpty do
        return none
      let some lhsIdx := hyps.idxOf? lhs | return none
      let some rhsIdx := hyps.idxOf? rhs | return none
      let lVars ← lVarsRef.get
      let rVars ← rVarsRef.get
      if lVars.contains lhs && rVars.contains rhs then
        lVarsRef.modify (·.erase lhs)
        rVarsRef.modify (·.erase rhs)
      else
        if lVars.contains rhs && rVars.contains lhs then
          lVarsRef.modify (·.erase rhs)
          rVarsRef.modify (·.erase lhs)
        else
          return none
      trace[transport] "with subgoal relating `{Expr.fvar lhs}` and `{Expr.fvar rhs}`"
      return some {
        lhsIdx
        rhsIdx
        hypIdx := i
        hypsPos := hypsPos.toList
        relHyps := relHyps.toList
      }
    -- Checks if `hyp` is a valid "main goal".
    let go := forallTelescope (← hyp.getType) fun xs hypTy => do
      if h : hypTy matches .sort 0 ∧ 2 ≤ xs.size then
        isMainGoal? (← inferType xs[xs.size - 2]) (← inferType xs[xs.size - 1]) xs.pop.pop
      else if let mkApp2 _ lhs₁ rhs₁ := hypTy then
        isMainGoal? lhs₁ rhs₁ xs
      else if let some lastFVar := xs.back? then
        isMainGoal? (← inferType lastFVar) hypTy xs.pop
      else
        return none
    if let some mainSubgoal ← go then
      mainSubgoals := mainSubgoals.push mainSubgoal
  let lVars ← lVarsRef.get
  let rVars ← rVarsRef.get
  if !lVars.isEmpty || !rVars.isEmpty then
    throwError "Could not find subgoal(s) relating \
      `{lVars.toList.map Expr.fvar}` and `{rVars.toList.map Expr.fvar}`"
  let mkKeys (e : Expr) : MetaM (Array DiscrTree.Key) := do
    let e ← Core.transform e (pre := fun e ↦ do
      if let .fvar fvarId := e.getAppFn then
        if hyps.contains fvarId then
          return .done (DiscrTree.mkNoindexAnnotation e)
      return .continue e)
    DiscrTree.mkPath e
  let mut lhsKeys ← mkKeys lhs
  let mut rhsKeys ← mkKeys rhs
  if let .other rel := rel then
    let keys ← mkKeys rel
    lhsKeys := keys ++ lhsKeys
    rhsKeys := keys ++ rhsKeys
  let relKind := rel.toKind
  let lhsKey := ({ forward := true, relKind }, lhsKeys)
  let rhsKey := ({ forward := false, relKind }, rhsKeys)
  let keys :=
    match dir with
    | some true => [lhsKey]
    | some false => [rhsKey]
    | none => [lhsKey, rhsKey]
  return {
    keys
    prio
    levelParams, proof
    numHyps := hyps.size
    sharedVars := sharedVars.toList.map hyps.idxOf
    mainSubgoals
  }

def mkTransportLemma (type proof : Expr) (levelParams : Array Name) (dir : Option Bool)
    (prio : Nat) : MetaM TransportLemma := do
  forallTelescope type fun xs type => do
  -- If the conclusion is `Prop`, then this is a transport relation `lhs → rhs → Prop`.
  -- If the conclusion is a free variable, it is a lemma like `imp_imp_imp` or `forall_imp`,
  -- so we revert the last two variables.
  if type matches .sort 0 | .fvar _ | .app (.fvar _) _ then
    let type ← mkForallFVars xs[(xs.size-2)...xs.size] type
    return ← mkTransportLemmaCore xs.pop.pop type proof levelParams dir prio
  try
    -- Add a `transport` lemma in the "normal" way.
    mkTransportLemmaCore xs type proof levelParams dir prio
  catch e => try
    let some x := xs.back? | failure
    let type ← mkForallFVars #[x] type
    mkTransportLemmaCore xs.pop type proof levelParams dir prio
  catch _ =>
    -- If none of the methods work, we throw the error thrown by the "normal" attempt.
    throw e

def preprocessTransportLemma (proof : Expr) (fs : Array Syntax) :
    MetaM (Option Expr) := do
  let type ← instantiateMVars (← inferType proof)
  unless ← isProp type do
    return none
  try
    some <$> forallTelescope type fun xs type ↦ do
      Elab.Term.TermElabM.run' do
      let fs ← fs.mapM fun f ↦ withRef f do
        let f ← Elab.Term.elabTerm f none
        let .forallE _ d b _ ← inferType f | throwError "not a function: `{f}`"
        if b.hasLooseBVars then
          throwError "`{b}` contains a loose bound varialbe"
        return (d, b, f)
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      mkLambdaFVars xs <| ← go xs type 0 #[] fs
  catch _ =>
    return none
where
  go (xs : Array Expr) (type : Expr) (i : Nat) (hs : Array (Expr × Expr))
      (fs : Array (Expr × Expr × Expr)) : MetaM Expr := do
    if h : i < xs.size then
      let x := xs[i]
      let xType ← inferType x
      if let some (_, xType', f) ← fs.findM? fun (t, _) ↦ isDefEq t xType then
        let xName ← x.fvarId!.getUserName
        withLocalDeclD (xName.appendAfter "'") xType' fun x' ↦ do
          let eq ← mkAppOptM ``Eq #[xType', f.beta #[x], x']
          let rel ← mkAppOptM ``MapRel #[xType, xType', f, x, x']
          withLocalDeclD (xName.appendBefore "h") rel fun hx ↦ do
            let proof ← go xs type (i + 1) (hs.push (hx, eq)) fs
            if proof.containsFVar hx.fvarId! then
              mkLambdaFVars #[x', hx] proof
            else
              pure proof
      else
        go xs type (i + 1) hs fs
    else
      let mut simpTheorems : SimpTheoremsArray := {}
      for (h, eq) in hs do
        simpTheorems ← simpTheorems.addTheorem (.fvar h.fvarId!) (mkExpectedPropHint h eq)
      let ctx ← Simp.mkContext Simp.neutralConfig simpTheorems
      let (r, _) ← simp type ctx
      let type' ← Mathlib.Tactic.etaReduceAll r.expr
      let proof ← mkAppM ``Eq.mp #[← r.getProof, mkAppN proof xs]
      let (type', proof) ← id do
        match_expr type' with
        | eq@Eq α lhs rhs =>
          for (d, b, f) in fs do
            let mvar ← mkFreshExprMVar d
            if ← isDefEq (f.beta #[mvar]) lhs then
              return (← mkAppOptM ``MapRel #[d, b, f, ← instantiateMVars mvar, rhs], proof)
            if ← isDefEq (f.beta #[mvar]) rhs then
              let proof ← mkAppM ``Eq.symm #[proof]
              return (← mkAppOptM ``MapRel #[d, b, f, ← instantiateMVars mvar, lhs], proof)
          return (type', proof)
        | _ => pure (type', proof)
      if type' == type then
        throwError "`{type}` was not changed "
      return mkExpectedPropHint proof type'

def mkTransportLemmaFromConst (declName : Name) (dir : Option Bool) (prio : Nat) :
    MetaM TransportLemma := do
  let cinfo ← getConstInfo declName
  let us := cinfo.levelParams.map mkLevelParam
  let val := mkConst declName us
  mkTransportLemma cinfo.type val #[] dir prio

def mkTransportLemmaFromExpr (proof : Expr) (levelParams : Array Name) (dir : Option Bool)
    (prio : Nat := eval_prio default) : MetaM TransportLemma := do
  if proof.isConst then
    mkTransportLemmaFromConst proof.constName! dir prio
  else
    mkTransportLemma (← instantiateMVars (← inferType proof)) proof levelParams dir prio

def elabTransportTheorem (stx : Syntax) (dir : Option Bool) : Elab.TermElabM TransportLemma :=
  withReducible <| withRef stx do
  let (levelParams, proof) ← id do
    if stx.isIdent then
      if let some e ← Elab.Term.resolveId? stx (withInfo := true) then
        return (#[], e)
    Elab.Term.withoutModifyingElabMetaStateWithInfo do
    let e ← Elab.Term.elabTerm stx none
    Elab.Term.synthesizeSyntheticMVars (postpone := .no) (ignoreStuckTC := true)
    let e ← instantiateMVars e
    let e := e.eta
    if e.hasMVar then
      let r ← abstractMVars e
      return (r.paramNames, r.expr)
    else
      return (#[], e)
  mkTransportLemmaFromExpr proof levelParams dir

/-- Attribute marking transport lemmas. -/
syntax (name := transportAttr) "transport" (ppSpace prio)? term,* : attr

/-- Mark `declName` with the `transport` attribute. -/
def addTransportLemma (declName : Name) (stx : Syntax) (kind : AttributeKind) : MetaM Unit :=
  withReducible do
  let `(attr| transport $[$prio:prio]? $[$fs],*) := stx | Elab.throwUnsupportedSyntax
  let prio ← getAttrParamOptPrio stx[1]
  let cinfo ← getConstInfo declName
  let const := .const declName (cinfo.levelParams.map .param)
  let declName ←
    if let some proof ← preprocessTransportLemma const fs then
      mkAuxLemma cinfo.levelParams (← inferType proof) proof (kind? := `transport)
    else
      pure declName
  let lem ← mkTransportLemmaFromConst declName (dir := none) prio
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
def makeGCongrGoal (rel : Rel) (e : Expr) (forward : Bool) : MetaM (Expr × Expr) := do
  match rel with
  | .other rel =>
    let .forallE _ d₁ (.forallE _ d₂ _ _) _ ← whnf (← inferType rel) | throwFunctionExpected rel
    -- note that `@[gcongr]`'s checks should prevent this happening
    if d₂.hasLooseBVars then throwError "grw: {rel} is a dependent relation"
    if forward then
      let mvar ← mkFreshExprMVar d₂
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel e mvar)
    else
      let mvar ← mkFreshExprMVar d₁
      return (mvar, ← mkFreshExprMVar <| mkApp2 rel mvar e)
  | .eq =>
    let ty ← inferType e
    let u ← getLevel ty
    let mvar ← mkFreshExprMVar (← inferType e)
    let eq :=
      if forward then mkApp3 (.const ``Eq [u]) ty e mvar else mkApp3 (.const ``Eq [u]) ty mvar e
    return (mvar, ← mkFreshExprMVar (some eq))
  | .relation =>
    let mvar ← mkFreshTypeMVar
    let (α, β) := if forward then (e, mvar) else (mvar, e)
    let target := .forallE `_ α (.forallE `_ β (.sort 0) .default) .default
    return (mvar, ← mkFreshExprMVar (some target))
  | .imp =>
    let mvar ← mkFreshTypeMVar
    let target := if forward then .forallE `_a e mvar .default else .forallE `_a mvar e .default
    return (mvar, ← mkFreshExprMVar (some target))


mutual

/-- Recursively call `transportCore` to process a subgoal of a `gcongr` lemma.

Returns whether we have done a rewrite in this subgoal, in which case it has been closed. -/
partial def processTransportHypothesis (goal : MVarId) : TransportM Bool := do
  let some (rel, lhs, rhs) := getRel' (← instantiateMVars (← goal.getType)) |
    throwError "invalid transport goal {goal}"
  let forward ← match lhs.getAppFn.isMVar, rhs.getAppFn.isMVar with
    | false, true => pure true
    | true, false => pure false
    | _, _ => throwError "expected exactly one of `{lhs}` and `{rhs}` to be unassigned."
  let (target, mvarApp) := if forward then (lhs, rhs) else (rhs, lhs)
  let some (result, proof) ← transportCoreOrRfl rel target forward |
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
partial def processGCongrLemma (e : Expr) (rel : Rel)
    (lem : TransportLemma) (forward : Bool) : TransportM (Option (Expr × Expr)) :=
  withTraceNode `transport (fun _ ↦
    return m!"applying transport lemma `{lem.proof}`") do
  let (mvar, goal) ← makeGCongrGoal rel e forward
  let (mainGoals, sideGoals) ←
    try
      applyGCongrLemma goal.mvarId! lem forward
    catch e =>
      trace[transport] "Error while applying `{lem.proof}`:\n{e.toMessageData}"
      return none
  -- Recursively rewrite in the main subgoals
  for (goal, relHyps) in mainGoals do
    let success ←
      goal.withContext <| withTransportHyps relHyps goal <| processTransportHypothesis
    unless success do
      return none
  let result ← instantiateMVars mvar
  if result == e then
    return none
  -- Finally, run the discharger on the side goals.
  for mvarId in sideGoals do
    if ← mvarId.isAssigned then
      continue
    let type ← mvarId.getType
    -- There may be instance side goals that still had metavariables before recursively rewriting.
    if (← isClass? type).isSome then
      if let .some inst ← trySynthInstance type then
        mvarId.assign inst
        continue
    dischargeSide mvarId
  return (result, goal)

partial def useTransportHyp (hyp : Expr) (goal : MVarId) (forward : Bool) : TransportM Bool := do
  let type := (← instantiateMVars (← inferType hyp)).headBeta
  if type.isAppOfArity ``FunctionRel 8 then
    let (mvars, _, _) ← withDefault <| forallMetaTelescopeReducing type (some 3)
    if ← useTransportHyp (mkAppN hyp mvars) goal forward then
      let some (rel, lhs, rhs) := getRel' (← instantiateMVars (← inferType mvars[2]!))
        | return false
      let e := if forward then rhs else lhs
      let some (result, proof) ← transportCoreOrRfl rel e forward
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
partial def transportCore (rel : Rel) (e : Expr) (forward : Bool) (inSimp := false) :
    TransportM (Option (Expr × Expr)) := do
  if !inSimp && rel matches .eq then
    if forward then
      transportEqCore e
    else
      (← transportEqCore e).mapM fun (e', pf) ↦ return (e', ← mkAppM ``Eq.symm #[pf])
  else
  let e := e.cleanupAnnotations
  if let .fvar fvarId := e.getAppFn then
    if let some hyp := (← read).transportHyps.get? fvarId then
      let mctx ← getMCtx
      let (mvar, goal) ← makeGCongrGoal rel e forward
      -- TODO: try `.applySymm` on the goal if this fails: might be needed for dual relations?
      if ← useTransportHyp (.fvar hyp) goal.mvarId! forward then
        trace[transport] "rewriting `{e}` to `{mvar}`"
        return some (← instantiateMVars mvar, goal)
      setMCtx mctx
  -- Try all applicable `@[transport]` lemmas.
  let lemmas ← findTransportLemmas? rel e forward
  let mctx ← getMCtx
  for gcongrLem in lemmas do
    if let some (result, proof) ← processGCongrLemma e rel gcongrLem forward then
      -- Preserve the binder name/info in a forall.
      match e, result with
      | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, proof)
      | _, _ => return some (result, proof)
    setMCtx mctx
  if rel matches .eq then
    -- Use `Eq.symm`, and then try again to find an applicable lemma
    let lemmas ← findTransportLemmas? rel e (!forward)
    let mctx ← getMCtx
    for gcongrLem in lemmas do
      if let some (result, proof) ← processGCongrLemma e rel gcongrLem (!forward) then
        let proof ← mkAppM ``Eq.symm #[proof]
        -- Preserve the binder name/info in a forall.
        match e, result with
        | .forallE n _ _ bi, .forallE _ d b _ => return some (.forallE n d b bi, proof)
        | _, _ => return some (result, proof)
      setMCtx mctx
  if rel matches .imp then
    if let some (e', pf) ← transportEqCore e then
      return some (e', ← mkAppM (if forward then ``Eq.mp else ``Eq.mpr) #[pf])
  return none

partial def transportEqCore (e : Expr) : TransportM (Option (Expr × Expr)) := fun c c' s ↦ do
  withTraceNodeBefore `transport (fun _ ↦
    return m!"visiting all subexpressions of `{e}` in the RHS of `_ = _`") do
  let methods := { pre e := do
    unless e.isApp || e.isForall || e.isFVar do return .continue
    let some (e', pf) ←
        transportCore .eq e true true c c' s |
      return .continue
    return .done { expr := e', proof? := pf }
    }
  let (r, _) ← Simp.main e (← Simp.mkContext Simp.neutralConfig) (methods := methods)
  let transportVars := c.transportHyps
  if r.expr.hasAnyFVar transportVars.contains then
    return none
  return r.proof?.map (r.expr, ·)

partial def transportCoreOrRfl (rel : Rel) (e : Expr) (forward : Bool) :
    TransportM (Option (Expr × Expr)) := do
  withTraceNodeBefore `transport (fun _ ↦
    return m!"visiting `{e}` in the {if forward then "LHS" else "RHS"} of `{rel}`") do
  if let some result ← transportCore rel e forward then
    trace[transport] "result: `{result.1}`"
    return result
  let transportVars := (← read).transportHyps
  if e.hasAnyFVar transportVars.contains then
    return none
  let pf ←
    match rel with
    | .eq =>
      let ty ← inferType e
      pure <| mkApp2 (.const ``Eq.refl [← getLevel ty]) ty e
    | .imp => pure <| .lam `_ e (.bvar 0) .default
    | .relation => pure <| .app (.const ``Eq [← getLevel e]) e
    | .other rel =>
      let mvar ← mkFreshExprMVar (mkApp2 rel e e)
      try
        -- Due to an issue in `rfl`, we need this transparency bump. See https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/.60with_reducible.20rfl.60.20failing/with/590957602
        withImplicit mvar.mvarId!.applyRfl
        instantiateMVars mvar
      catch _ =>
        return none
  trace[transport] "transporting `{e}` to itself"
  return some (e, pf)

end

open Elab Tactic

public syntax transportClause := ("→ " <|> "← ")? term --(" to " term)?

syntax "transport" (" [" transportClause,* "]")?
  (" generalizing" (ppSpace colGt ident)*)? : tactic

elab_rules : tactic
| `(tactic| transport $[[$[$args],*]]? $[generalizing $xs*]?) => do
  let mut terms : Array (Term × Option Bool) := #[]
  -- let mut clauses := #[]
  for arg in args.getD #[] do
    match arg with
    | `(transportClause| → $e:term) => terms := terms.push (e, some true)
    | `(transportClause| ← $e:term) => terms := terms.push (e, some false)
    | `(transportClause| $e:term) => terms := terms.push (e, none)
    -- | `(transportClause| $α:term to $β) => clauses := clauses.push (α, β)
    | _ => throwUnsupportedSyntax
  let mvarId ← getMainGoal
  let tag ← mvarId.getTag
  let (mvarId, intros) ← mvarId.withContext do
    let fvarIds ← (xs.getD #[]).mapM (getFVarId ·.raw)
    let fvarIds ← sortFVarIds fvarIds
    let (fvarIds, mvarId) ← mvarId.revert fvarIds (preserveOrder := true)
    pure (mvarId, fvarIds.size)
  mvarId.withContext do
  let givenLemmas ← terms.mapM fun (e, dir) ↦ elabTransportTheorem e dir
  let lemmas := transportExt.getState (← getEnv)
  let lemmas := givenLemmas.foldl addTransportLemmaEntry lemmas
  let type ← instantiateMVars (← mvarId.getType)
  let (some (e, pf), s) ← withReducible <|
    transportCore .imp type false |>.run { lemmas } |>.run
    | throwError "transport made no progress on `{type}`"
  let newGoal ← mkFreshExprMVar e .syntheticOpaque
  mvarId.assign (pf.app newGoal)
  let (_, newGoal) ← newGoal.mvarId!.introNP intros
  newGoal.setTag tag
  let mctx ← getMCtx
  replaceMainGoal ((s.newGoals.filter mctx.decls.contains).toList ++ [newGoal])


end Test
