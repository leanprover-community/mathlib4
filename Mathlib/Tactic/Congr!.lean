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
Like `Lean.MVarId.congr?` but instead of using only the congruence lemma associated to the LHS,
it tries the RHS too. Uses `Lean.Meta.mkCongrSimp?` to generate a congruence lemma.

Applies the congruence generated congruence lemmas using reducible transparency.
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
    observing? do
      let side := side.cleanupAnnotations
      if not side.isApp then failure
      let some congrThm ← mkCongrSimp? side.getAppFn (subsingletonInstImplicitRhs := false)
          | failure
      applyCongrThm? config mvarId congrThm.type congrThm.proof

/--
Like `Lean.MVarId.hcongr?` but applies symmetrically like `Lean.MVarId.congrSimp?`.

If the goal is an `Eq`, uses `eq_of_heq` first, since there are cases where `heq` congruency
lemmas are more powerful than `Eq` ones.

Applies the congruence generated congruence lemmas using reducible transparency.
-/
def Lean.MVarId.hcongr?' (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `hcongr?
    observing? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | failure
      let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
      if let some mvars ← forSide mvarId fst then
        return mvars
      else if let some mvars ← forSide mvarId snd then
        return mvars
      else
        failure
where
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) :=
    observing? do
      let side := side.cleanupAnnotations
      if not side.isApp then failure
      let congrThm ← mkHCongr side.getAppFn
      applyCongrThm? config mvarId congrThm.type congrThm.proof

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
There are instances where `Lean.MVarId.simpCongr?` might fail, and this is a fallback sort of like
the fallback behavior present in the `simp` tactic, but with a simpler implementation.
(For example of failure, there is issue lean4#2128 where
congruence lemmas aren't generated correctly for partially applied functions.)

Unlike `Lean.MVarId.congr?` (and unlike the `simp` fallback), we use both the LHS and the RHS
to drive the congruence generation.

(See `Lean.Meta.Simp.simp.congrArgs` for the `simp` congruence fallback.)
-/
partial
def Lean.MVarId.fallbackCongr? (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    mvarId.checkNotAssigned `fallbackCongr
    let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? | failure
    let (steps, pf, goals) ← loop lhs rhs
    if steps == 0 then
      -- Nothing was handled, so fail
      failure
    -- The following *should* suceed if we implemented `loop` correctly.
    guard (← isDefEq (← inferType <| mkMVar mvarId) (← inferType pf))
    mvarId.assign pf
    -- Note: we might be left with eta-unexpanded things like `HAdd.hAdd 1`, but we can't
    -- use `Meta.etaExpand` here since this will just trigger `obviousFunext?` and start
    -- an infinite loop in `congr!`.
    return goals
where
  default (lhs rhs : Expr) : MetaM (Nat × Expr × List MVarId) := do
    let pf ← mkFreshExprMVar (some (← mkEq lhs rhs))
    return (0, pf, [pf.mvarId!])
  loop (lhs rhs : Expr) : MetaM (Nat × Expr × List MVarId) :=
    match lhs.cleanupAnnotations, rhs.cleanupAnnotations with
    | .app lhs a, .app rhs b => do
      -- It only makes sense to continue if the types of the arguments are the same.
      unless ← withNewMCtxDepth <| isDefEq (← inferType a) (← inferType b) do
        return ← default lhs rhs
      let tylhs ← whnfD (← inferType lhs)
      let tyrhs ← whnfD (← inferType rhs)
      -- And also if the types of the functions are the same.
      unless ← withNewMCtxDepth <| isDefEq tylhs tyrhs do
        return ← default lhs rhs
      -- Next, if the arguments themselves are the same, we can use `congrFun`.
      let argeq ← withNewMCtxDepth <| isDefEq a b
      if argeq then
        let (steps, pf, accGoals) ← loop lhs rhs
        let pf ← Meta.mkCongrFun pf a
        --guard (← isDefEq (mkMVar mvarId) pf)
        return (steps + 1, pf, accGoals)
      -- Now we can try `congr` if the functions are non-dependent
      if tylhs.isArrow && tyrhs.isArrow then
        let (steps, pf, accGoals) ← loop lhs rhs
        let eq ← mkFreshExprMVar (some (← mkEq a b))
        let pf ← Meta.mkCongr pf eq
        return (steps + 1, pf, accGoals ++ [eq.mvarId!])
      -- All these checks failed, so we have to stop here.
      default lhs rhs
    | lhs, rhs => default lhs rhs

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
   ("congr simp lemma", congrSimp?),
   ("fallback congr lemma", fun _ => fallbackCongr?),
   ("hcongr lemma", hcongr?'),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfunext", fun _ => obviousHfunext?),
   ("congr_implies", fun _ => congrImplies?),
   ("congr_pi", fun _ => congrPi?)]

/-- Convert a goal into an `Eq` goal if possible (since we have a better shot at those).
Also try to dispatch the goal using an assumption, `Subsingleton.Elim`, or definitional equality. -/
def Lean.MVarId.preCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  -- User congr lemmas might have created additional hypotheses.
  let (_, mvarId) ← mvarId.intros
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

def Lean.MVarId.congrCore! (config : Congr!.Config) (depth : Nat) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want it to stick
     if there are no relevant congr lemmas. -/
  mvarId.checkNotAssigned `congr!
  trace[congr!] "congrCore! [{depth}] {mvarId}"
  let s ← saveState
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some mvarIds ← pass config mvarId then
        trace[congr!] "  pass succeded: {passName}"
        return mvarIds
    catch e =>
      throwTacticEx `congr! mvarId
        m!"internal error in congruence pass {passName}, {e.toMessageData}"
    if ← mvarId.isAssigned then
      throwTacticEx `congr! mvarId
        s!"congruence pass {passName} assigned metavariable but failed"
  restoreState s
  trace[congr!] "  no passes succeeded"
  return none

/-- A pass to clean up after `Lean.MVarId.preCongr!` and `Lean.MVarId.congrCore!`. -/
def Lean.MVarId.postCongr! (mvarId : MVarId) : MetaM (Option MVarId) := do
  let some mvarId ← mvarId.preCongr! | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if ← mvarId.assumptionCore then return none
  return some mvarId

/-- A more insistent version of `Lean.MVarId.congrN`.
See the documentation on the `congr!` syntax. -/
def Lean.MVarId.congrN! (mvarId : MVarId) (depth : Nat := 1000000) (config : Congr!.Config := {}) :
    MetaM (List MVarId) := do
  let (_, s) ← go depth mvarId |>.run #[]
  return s.toList
where
  post (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← mvarId.postCongr! | return
    modify (·.push mvarId)
  go (n : Nat) (mvarId : MVarId) : StateRefT (Array MVarId) MetaM Unit := do
    let some mvarId ← withTransparency config.preTransparency mvarId.preCongr! | return
    match n with
      | 0 => post mvarId
      | n + 1 =>
        let some mvarIds ← mvarId.congrCore! config (n+1)
          | post mvarId
        mvarIds.forM (go n)

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
  let hugeDepth := 1000000
  let depth := n.map (·.getNat) |>.getD hugeDepth
  liftMetaTactic fun g ↦ g.congrN! depth config

end Congr!
