/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Tactic.Relation.Rfl
import Std.Logic

/-!
# The `congr!` tactic

This is a more powerful version of the `congr` tactic that knows about more congruence lemmas and
can apply to more situations. It is similar to the `congr'` tactic from Mathlib 3.

The `congr!` tactic is used by the `convert` and `convert_to` tactics.

See the syntax docstring for more details.
-/

open Lean Meta Elab Tactic

initialize registerTraceClass `congr!

/-- The configuration for the `congr!` tactic. -/
structure Congr!.Config where
  /-- The transparency level to use when applying a congruence theorem.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  transparency : TransparencyMode := TransparencyMode.reducible
  /-- The transparency level to use when doing transformations before applying congruence lemmas.
  This includes trying to prove the goal by `rfl` and using the `assumption` tactic.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  preTransparency : TransparencyMode := TransparencyMode.reducible
  /-- For passes that synthesize a congruence lemma using one side of the equality,
  we run the pass both for the left-hand side and the right-hand side. If `preferLHS` is `true`
  then we start with the left-hand side.

  This can be used to control which side's definitions are expanded when applying the
  congruence lemma (if `preferLHS = true` then the RHS can be expanded). -/
  preferLHS : Bool := true

/--
Asserts the given congruence theorem as fresh hypothesis, and then applies it.
Return the `fvarId` for the new hypothesis and the new subgoals.

We apply it with transparency settings specified by `Congr!.Config.transparency`.
-/
private def applyCongrThm?
    (config : Congr!.Config) (mvarId : MVarId) (congrThmType congrThmProof : Expr) :
    MetaM (List MVarId) := do
  trace[congr!] "trying to apply congr lemma {congrThmType}"
  try
    let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThmType congrThmProof
    let (fvarId, mvarId) ← mvarId.intro1P
    let mvarIds ← withTransparency config.transparency <|
      mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
    mvarIds.mapM fun mvarId => mvarId.tryClear fvarId
  catch e =>
    withTraceNode `congr! (fun _ => pure m!"failed to apply congr lemma") do
      trace[congr!] "{e.toMessageData}"
    throw e

/--
Create a congruence lemma to prove that `HEq (f a₁ ... aₙ) (f' a₁' ... aₙ')`.
Each argument produces a `HEq aᵢ aᵢ'` hypothesis, but we also supply these hypotheses the
hypotheses that the preceding equalities have been proved (unlike in `mkHCongrWithArity`).
The first two arguments of the resulting theorem are for `f` and `f'`, followed by a proof
of `f = f'`.

When including hypotheses about previous hypotheses, we make use of dependency information
and only include relevant equalities.

The argument `fty` denotes the type of `f`. Returns `(congrThmType, congrThmProof)`.
-/
partial def Congr!.mkHCongrThm (fType : Expr) (info : FunInfo) :
    MetaM (Expr × Expr) := do
  --trace[congr!] "ftype: {fType}"
  --trace[congr!] "deps: {info.paramInfo.map (fun p => p.backDeps)}"
  forallBoundedTelescope fType info.getArity fun xs _ =>
  forallBoundedTelescope fType info.getArity fun ys _ => do
    if xs.size != info.getArity then
      throwError "failed to generate hcongr theorem, insufficient number of arguments"
    let lctx := withDefaultBinderInfo (xs ++ ys) <| addPrimesToUserNames ys (← getLCtx)
    withLCtx lctx (← getLocalInstances) do
    withLocalDeclD `f fType fun ef =>
    withLocalDeclD `f' fType fun ef' => do
    withLocalDeclD `e (← mkEq ef ef') fun ee => do
    withNewEqs xs ys fun eqs eqs' vals => do
      let mut hs := #[ef, ef', ee]
      let mut hs' := hs
      let mut vals' := hs
      for i in [0 : info.getArity] do
        hs := hs.push xs[i]! |>.push ys[i]! |>.push eqs[i]!
        hs' := hs'.push xs[i]! |>.push ys[i]! |>.push eqs'[i]!
        vals' := vals'.push xs[i]! |>.push ys[i]! |>.push vals[i]!
      let lhs := mkAppN ef xs
      let rhs := mkAppN ef' ys
      -- Generate the theorem with respect to the simpler hypotheses
      let congrType ← mkForallFVars hs (← mkHEq lhs rhs)
      let proof ← mkProof congrType
      -- Now transform the theorem to be respect to the richer hypotheses
      let congrType' ← mkForallFVars hs' (← mkHEq lhs rhs)
      let proof' ← mkLambdaFVars hs' (← mkAppM' proof vals')
      return (congrType', proof')
where
  addPrimesToUserNames (ys : Array Expr) (lctx : LocalContext) : LocalContext := Id.run do
    let mut lctx := lctx
    for y in ys do
      let decl := lctx.getFVar! y
      lctx := lctx.setUserName decl.fvarId (decl.userName.appendAfter "'")
    return lctx
  withDefaultBinderInfo (xs : Array Expr) (lctx : LocalContext) : LocalContext := Id.run do
    return xs.foldl (fun lctx y => lctx.setBinderInfo y.fvarId! .default) lctx
  withNewEqs {α} (xs ys : Array Expr)
      (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α :=
    let rec loop (i : Nat) (eqs eqs' vals : Array Expr) := do
      if i < xs.size then
        let x := xs[i]!
        let y := ys[i]!
        let deps := info.paramInfo[i]!.backDeps.map (fun j => eqs[j]!)
        let deps' := info.paramInfo[i]!.backDeps.map (fun j => vals[j]!)
        let eq' ← mkForallFVars deps (← mkHEq x y)
        withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkHEq x y) fun h =>
        withLocalDeclD ((`e').appendIndexAfter (i+1)) eq' fun h' =>
          -- vals is how to compute eqs from eqs'
          let v := mkAppN h' deps'
          loop (i+1) (eqs.push h) (eqs'.push h') (vals.push v)
      else
        k eqs eqs' vals
    loop 0 #[] #[] #[]
  mkProof (type : Expr) : MetaM Expr := do
    if let some (_, lhs, _, _) := type.heq? then
      return ← mkHEqRefl lhs
    unless type.isForall do
      throwError "Internal error, expecting forall type"
    forallBoundedTelescope type (some 1) fun a type =>
    let a := a[0]!
    forallBoundedTelescope type (some 1) fun b motive =>
    let b := b[0]!
    let type := type.bindingBody!.instantiate1 a
    withLocalDeclD motive.bindingName! motive.bindingDomain! fun eqPr => do
    let major ← (if motive.bindingDomain!.isHEq then mkEqOfHEq else pure) eqPr
    let minor ← mkProof type.bindingBody!
    let motive ← mkLambdaFVars #[b] motive.bindingBody!
    mkLambdaFVars #[a, b, eqPr] (← mkEqNDRec motive minor major)

/--
Like `Lean.MVarId.congr?` but instead of using only the congruence lemma associated to the LHS,
it tries the RHS too, in the order specified by `config.preferLHS`.

It uses `Lean.Meta.mkCongrSimp?` to generate a congruence lemma, like in the `congr` tactic.

Applies the congruence generated congruence lemmas according to `config`.
-/
def Lean.MVarId.congrSimp? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congrSimp?
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide mvarId fst then
      return mvars
    else if let some mvars ← forSide mvarId snd then
      return mvars
    else
      return none
where
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) :=
    commitWhenSome? do
      let side := side.cleanupAnnotations
      if not side.isApp then return none
      let some congrThm ← mkCongrSimpNArgs side.getAppFn side.getAppNumArgs
        | return none
      observing? <| applyCongrThm? config mvarId congrThm.type congrThm.proof
  /-- Like `mkCongrSimp?` but takes in a specific arity. -/
  mkCongrSimpNArgs (f : Expr) (nArgs : Nat) : MetaM (Option CongrTheorem) := do
    let f := (← instantiateMVars f).cleanupAnnotations
    let info ← getFunInfoNArgs f nArgs
    mkCongrSimpCore? f info
      (← getCongrSimpKinds f info) (subsingletonInstImplicitRhs := false)

/--
Try applying user-provided congruence lemmas. If any are applicable,
returns a list of new goals.

Tries a congruence lemma associated to the LHS and then, if that failed, the RHS.
-/
def Lean.MVarId.userCongr? (config : Congr!.Config)  (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `userCongr?
    let some (lhs, rhs) := (← withReducible mvarId.getType').eqOrIff? | return none
    let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
    if let some mvars ← forSide fst then
      return mvars
    else if let some mvars ← forSide snd then
      return mvars
    else
      return none
where
  forSide (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let some name := side.getAppFn.constName? | return none
    let congrTheorems := (← getSimpCongrTheorems).get name
    -- Note: congruence theorems are provided in decreasing order of priority.
    for congrTheorem in congrTheorems do
      let res ← observing? do
        let cinfo ← getConstInfo congrTheorem.theoremName
        let us ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
        let proof := mkConst congrTheorem.theoremName us
        let ptype ← instantiateTypeLevelParams cinfo us
        applyCongrThm? config mvarId ptype proof
      if let some mvars := res then
        return mvars
    return none

/--
This is like `Lean.MVarId.hcongr?` but (1) looks at both sides when generating the congruence lemma
and (2) inserts additional hypotheses from equalities from previous arguments.

If the goal is an `Eq`, uses `eq_of_heq` first.
-/
partial
def Lean.MVarId.smartHCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs then
        return mvars
      -- That failed, which is the "correct" behavior. However, it's often useful
      -- to apply congruence lemmas while unfolding definitions, which is what the
      -- basic `congr` tactic does due to limitations in how congruence lemmas are generated.
      -- We simulate this behavior here by generating congruence lemmas for the LHS and RHS and
      -- applying them.
      if config.transparency == .reducible then
        return none
      trace[congr!] "Default smartHCongr? failed, trying LHS/RHS method"
      let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
      if let some mvars ← forSide mvarId fst then
        return mvars
      else if let some mvars ← forSide mvarId snd then
        return mvars
      else
        return none
where
  loop (mvarId : MVarId) (numArgs : Nat) (lhs rhs : Expr) : MetaM (Option (List MVarId)) :=
    match lhs.cleanupAnnotations, rhs.cleanupAnnotations with
    | .app f _, .app f' _ => do
      -- We try to generate a theorem for the maximal number of arguments
      if let some mvars ← loop mvarId (numArgs + 1) f f' then
        return mvars
      -- That failing, we now try for the present number of arguments, so long as the
      -- types of the functions are definitionally equal.
      unless ← withNewMCtxDepth <| isDefEq (← inferType f) (← inferType f') do
        return none
      let info ← getFunInfoNArgs f (numArgs + 1)
      let (congrThm, congrProof) ← Congr!.mkHCongrThm (← inferType f) info
      -- Now see if the congruence theorem actually applies in this situation by applying it!
      let congrThm' := congrThm.bindingBody!.bindingBody!.instantiateRev #[f, f']
      let congrProof' := mkApp2 congrProof f f'
      observing? <| applyCongrThm? config mvarId congrThm' congrProof'
    | _, _ => return none
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) := do
      let side := side.cleanupAnnotations
      if not side.isApp then return none
      let f := side.getAppFn
      let info ← getFunInfoNArgs f side.getAppNumArgs
      let (congrThm, congrProof) ← Congr!.mkHCongrThm (← inferType f) info
      let r ← mkEqRefl f
      let congrThm' := congrThm.bindingBody!.bindingBody!.instantiateRev #[f, f, r]
      let congrProof' := mkApp3 congrProof f f r
      observing? <| applyCongrThm? config mvarId congrThm' congrProof'

/--
Try to convert an `Iff` into an `Eq` by applying `iff_of_eq`.
If successful, returns the new goal, and otherwise returns the original `MVarId`.

This may be regarded as being a special case of `Lean.MVarId.liftReflToEq`, specifically for `Iff`.
-/
def Lean.MVarId.iffOfEq (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    let [mvarId] ← mvarId.apply (mkConst ``iff_of_eq []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to convert an `Eq` into an `Iff` by applying `propext`.
If successful, then returns then new goal, otherwise returns the original `MVarId`.
-/
def Lean.MVarId.propext (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    -- Avoid applying `propext` if the target is not an equality of `Prop`s.
    -- We don't want a unification specializing `Sort _` to `Prop`.
    let tgt ← withReducible mvarId.getType'
    let some (ty, _, _) := tgt.eq? | failure
    guard ty.isProp
    let [mvarId] ← mvarId.apply (mkConst ``propext []) | failure
    return mvarId
  return res.getD mvarId

/-- Helper theorem for `Lean.MVar.liftReflToEq`. -/
theorem Lean.MVarId.rel_of_eq_and_refl {R : α → α → Prop} (hxy : x = y) (h : R x x) :
    R x y := hxy ▸ h

/--
Use a `refl`-tagged lemma to convert the goal into an `Eq`. If this can't be done, returns
the original `MVarId`.
-/
def Lean.MVarId.liftReflToEq (mvarId : MVarId) : MetaM MVarId := do
  mvarId.checkNotAssigned `liftReflToEq
  let tgt ← withReducible mvarId.getType'
  let .app (.app rel _) _ := tgt | return mvarId
  if rel.isAppOf `Eq then
    -- No need to lift Eq to Eq
    return mvarId
  let reflLemmas ← (Mathlib.Tactic.reflExt.getState (← getEnv)).getMatch rel
  for lem in reflLemmas do
    let res ← observing? do
      -- First create an equality relating the LHS and RHS
      -- and reduce the goal to proving that LHS is related to LHS.
      let [mvarIdEq, mvarIdR] ←
            mvarId.apply (← mkConstWithFreshMVarLevels ``Lean.MVarId.rel_of_eq_and_refl)
        | failure
      -- Then fill in the proof of the latter by reflexivity.
      let [] ← mvarIdR.apply (← mkConstWithFreshMVarLevels lem) | failure
      return mvarIdEq
    if let some mvarId := res then
      return mvarId
  return mvarId

/--
Try to close the goal using `Subsingleton.elim`. Returns whether or not it succeeds.

We are careful to apply `Subsingleton.elim` in a way that does not assign any metavariables.
This is to prevent the `Subsingleton Prop` instance from being used as justification to specialize
`Sort _` to `Prop`.
-/
def Lean.MVarId.subsingletonElim (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `subsingletonElim
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, rhs) := tgt.eq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which we depend on to avoid unification.
      let pf ← mkAppM ``Subsingleton.elim #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

/--
Try to close the goal with using `proof_irrel_heq`. Returns whether or not it succeeds.

We need to be somewhat careful not to assign metavariables while doing this, otherwise we might
specialize `Sort _` to `Prop`.
-/
def Lean.MVarId.proofIrrelHeq (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `proofIrrelHeq
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, _, rhs) := tgt.heq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which we depend on to avoid unification.
      let pf ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

/--
Try to apply `pi_congr`. This is similar to `Lean.MVar.congrImplies?`.
-/
def Lean.MVarId.congrPi? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do withReducible <| mvarId.apply (← mkConstWithFreshMVarLevels `pi_congr)

/--
Try to apply `funext`, but only if it is an equality of two functions where at least one is
a lambda expression.

One thing this check prevents is accidentally applying `funext` to a set equality, but also when
doing congruence we don't want to apply `funext` unnecessarily.
-/
def Lean.MVarId.obviousFunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels ``funext)

/--
Try to apply `Function.hfunext`, returning the new goals if it succeeds.
Like `Lean.MVarId.obviousFunext?`, we only do so if at least one side of the `HEq` is a lambda.
This prevents unfolding of things like `Set`.

Need to have `Mathlib.Logic.Function.Basic` imported for this to succeed.
-/
def Lean.MVarId.obviousHfunext? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
    if not lhs.cleanupAnnotations.isLambda && not rhs.cleanupAnnotations.isLambda then failure
    mvarId.apply (← mkConstWithFreshMVarLevels `Function.hfunext)

/--
A list of all the congruence strategies used by `Lean.MVarId.congrCore!`.
-/
def Lean.MVarId.congrPasses! :
    List (String × (Congr!.Config → MVarId → MetaM (Option (List MVarId)))) :=
  [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   --("congr simp lemma", congrSimp?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfunext", fun _ => obviousHfunext?),
   ("congr_implies", fun _ => congrImplies?),
   ("congr_pi", fun _ => congrPi?)]

/--
Does `Lean.MVarId.intros` but then cleans up the introduced hypotheses, removing anything
that is trivial.

Cleaning up includes:
- deleting hypotheses of the form `HEq x x`, `x = x`, and `x ↔ x`.
- converting `HEq x y` to `x = y` if possible.
- converting `x = y` to `x ↔ y` if possible.
-/
partial
def Lean.MVarId.introsClean (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
  loop #[] mvarId
where
  loop (fvars : Array FVarId) (mvarId : MVarId) : MetaM (Array FVarId × MVarId) :=
    mvarId.withContext do
      let ty ← withReducible <| mvarId.getType'
      match ty with
      | .forallE .. => do
        if ty.isArrow && (← isTrivialType ty.bindingDomain!) then
          if let some mvarId ← tryConst mvarId then
            return ← loop fvars mvarId
        let mvarId ← (Option.getD · mvarId) <$> eqLift mvarId
        let mvarId ← (Option.getD · mvarId) <$> iffLift mvarId
        let (fvar, mvarId) ← mvarId.intro1
        return (fvars.push fvar, mvarId)
      | _ => return (fvars, mvarId)
  isTrivialType (ty : Expr) : MetaM Bool := do
    let ty ← instantiateMVars ty
    unless ← Meta.isProp ty do
      return false
    if let some (lhs, rhs) := ty.eqOrIff? then
      if lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    if let some (α, lhs, β, rhs) := ty.heq? then
      if α.cleanupAnnotations == β.cleanupAnnotations
          && lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    return false
  tryConst (mvarId : MVarId) : MetaM (Option MVarId) :=
    observing? do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``Function.const)
        | failure
      return mvarId
  eqLift (mvarId : MVarId) : MetaM (Option MVarId) :=
    -- Given a goal of the form `HEq a b -> p`, turn it into `a = b -> p`.
    -- Returns none this can't be done.
    commitWhenSome? <| mvarId.withContext do
      mvarId.checkNotAssigned `introsClean
      let ty ← withReducible <| mvarId.getType'
      unless ty.isForall do return none
      let some (α, lhs, β, rhs) := ty.bindingDomain!.heq? | return none
      -- TODO: should we permanently unify here by removing withNewMCtxDepth?
      unless (← withNewMCtxDepth <| isDefEq α β) do return none
      let ty' ← withLocalDecl ty.bindingName! ty.bindingInfo! (← mkEq lhs rhs) fun e => do
        let e' := mkApp4 (mkConst ``heq_of_eq [← mkFreshLevelMVar]) α lhs rhs e
        mkForallFVars #[e] (ty.bindingBody!.instantiate1 e')
      let mvarId' ← mkFreshExprSyntheticOpaqueMVar ty' (← mvarId.getTag)
      withLocalDecl ty.bindingName! ty.bindingInfo! ty.bindingDomain! fun he => do
        let pf ← mkLambdaFVars #[he] (.app mvarId' (← mkEqOfHEq he))
        guard <| ← withNewMCtxDepth <| isDefEq ty (← inferType pf) -- safety check
        mvarId.assign pf
        return mvarId'.mvarId!
  iffLift (mvarId : MVarId) : MetaM (Option MVarId) :=
    -- Given a goal of the form `a = b -> p`, turn it into `(a ↔ b) -> p`.
    -- Returns none if this can't be done.
    commitWhenSome? <| mvarId.withContext do
      mvarId.checkNotAssigned `introsClean
      let ty ← withReducible <| mvarId.getType'
      unless ty.isForall do return none
      let some (α, lhs, rhs) := ty.bindingDomain!.eq? | return none
      unless (← withReducible <| whnf α).isProp do return none
      let iff := mkApp2 (.const ``Iff []) lhs rhs
      let ty' ← withLocalDecl ty.bindingName! ty.bindingInfo! iff fun e => do
        let e' ← mkPropExt e
        mkForallFVars #[e] (ty.bindingBody!.instantiate1 e')
      let mvarId' ← mkFreshExprSyntheticOpaqueMVar ty' (← mvarId.getTag)
      withLocalDecl ty.bindingName! ty.bindingInfo! ty.bindingDomain! fun he => do
        let pf ← mkLambdaFVars #[he] (.app mvarId' (← mkIffOfEq he))
        guard <| ← withNewMCtxDepth <| isDefEq ty (← inferType pf) -- safety check
        mvarId.assign pf
        return mvarId'.mvarId!

/-- Convert a goal into an `Eq` goal if possible (since we have a better shot at those).
Also try to dispatch the goal using an assumption, `Subsingleton.Elim`, or definitional equality. -/
def Lean.MVarId.preCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  -- Congr lemmas might have created additional hypotheses.
  let (_, mvarId) ← mvarId.introsClean
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  -- This is a good time to check whether we have a relevant hypothesis.
  if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  -- Now try definitional equality. No need to try `mvarId.hrefl` since we already did  `heqOfEq`.
  try mvarId.refl; return none catch _ => pure ()
  -- Now we go for (heterogenous) equality via subsingleton considerations
  if ← mvarId.subsingletonElim then return none
  if ← mvarId.proofIrrelHeq then return none
  return some mvarId

def Lean.MVarId.congrCore! (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want it to stick
     if there are no relevant congr lemmas. -/
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some mvarIds ← pass config mvarId then
        trace[congr!] "pass succeded: {passName}"
        return mvarIds
    catch e =>
      throwTacticEx `congr! mvarId
        m!"internal error in congruence pass {passName}, {e.toMessageData}"
    if ← mvarId.isAssigned then
      throwTacticEx `congr! mvarId
        s!"congruence pass {passName} assigned metavariable but failed"
  restoreState s
  trace[congr!] "no passes succeeded"
  return none

/-- A pass to clean up after `Lean.MVarId.preCongr!` and `Lean.MVarId.congrCore!`. -/
def Lean.MVarId.postCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  let some mvarId ← mvarId.preCongr! | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if ← mvarId.assumptionCore then return none
  return some mvarId

/-- A more insistent version of `Lean.MVarId.congrN`.
See the documentation on the `congr!` syntax.

The `depth?` argument controls the depth of the recursion. If `none`, then it uses a reasonably
large bound that is linear in the expression depth. -/
def Lean.MVarId.congrN! (mvarId : MVarId) (depth? : Option Nat) (config : Congr!.Config := {}) :
    MetaM (List MVarId) := do
  let ty ← withReducible <| mvarId.getType'
  -- A reasonably large yet practically bounded default recursion depth.
  let defaultDepth := max 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
  let (_, s) ← go depth depth mvarId |>.run #[]
  return s.toList
where
  post (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← mvarId.postCongr!
        | do trace[congr!] "Dispatched goal by post-processing step."
             return
    modify (·.push mvarId)
  go (depth : Nat) (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← withTransparency config.preTransparency mvarId.preCongr! | return
    match n with
      | 0 =>
        trace[congr!] "At level {depth - n}, doing post-processing. {mvarId}"
        post mvarId
      | n + 1 =>
        trace[congr!] "At level {depth - n}, trying congrCore!. {mvarId}"
        let some mvarIds ← mvarId.congrCore! config
          | post mvarId
        mvarIds.forM (go depth n)

namespace Congr!

declare_config_elab elabConfig Config

/--
Equates pieces of the left-hand side of a goal to corresponding pieces of the right-hand side by
recursively applying congruence lemmas. For example, with `⊢ f as = g bs` we could get
two goals `⊢ f = g` and `⊢ as = bs`.

The `congr!` tactic is similar to `congr` but is more insistent in trying to equate left-hand sides
to right-hand sides of goals. Here is a list of things it can try:

- If `R` in `⊢ R x y` is a reflexive relation, it will convert the goal to `⊢ x = y` if possible.
  The list of reflexive relations is maintained using the `@[refl]` attribute.
  As a special case, `⊢ p ↔ q` is converted to `⊢ p = q` during congruence processing and then
  returned to `⊢ p ↔ q` form at the end.

- If there is a user congruence lemma associated to the goal (for instance, a `@[congr]`-tagged
  lemma applying to `⊢ List.map f xs = List.map g ys`), then it will use that.

- Like `congr`, it makes use of the `Eq` and `HEq` congruence lemma generator internally used
  by `simp`. Hence, one can equate any two pieces of an expression that is accessible to `simp`.

- It uses `implies_congr` and `pi_congr` to do congruences of pi types.

- Before applying congruences, it will run the `intros` tactic automatically.
  The introduced variables can be given names using the `rename_i` tactic as needed.
  This helps when user congruence lemmas are applied, since they often provide
  additional hypotheses.

- When there is an equality between functions, so long as at least one is obviously a lambda, we
  apply `funext` or `Function.hfunext`, which allows for congruence of lambda bodies.

In addition, `congr!` tries to dispatch goals using a few strategies, including checking
definitional equality, trying to apply `Subsingleton.elim` or `proof_irrel_heq`, and using the
`assumption` tactic.

The optional parameter is the depth of the recursive applications.
This is useful when `congr!` is too aggressive in breaking down the goal.
For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
`congr!` produces the goals `⊢ x = y` and `⊢ y = x`,
while `congr! 2` produces the intended `⊢ x + y = y + x`.

The `congr!` tactic also takes a configuration option, for example
```lean
congr! (config := {transparency := .default}) 2
```
See `Congr!.Config` for options.
-/
syntax (name := congr!) "congr!" (Parser.Tactic.config)? (num)? : tactic

elab_rules : tactic
| `(tactic| congr! $[$cfg:config]? $[$n]?) => do
  let config ← elabConfig (mkOptionalNode cfg)
  liftMetaTactic fun g ↦
    let depth := n.map (·.getNat)
    g.congrN! depth config

end Congr!
