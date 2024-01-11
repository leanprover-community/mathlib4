/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean
import Mathlib.Tactic.Relation.Rfl
import Std.Logic
import Std.Tactic.RCases

/-!
# The `congr!` tactic

This is a more powerful version of the `congr` tactic that knows about more congruence lemmas and
can apply to more situations. It is similar to the `congr'` tactic from Mathlib 3.

The `congr!` tactic is used by the `convert` and `convert_to` tactics.

See the syntax docstring for more details.
-/

open Lean Meta Elab Tactic

initialize registerTraceClass `congr!
initialize registerTraceClass `congr!.synthesize

/-- The configuration for the `congr!` tactic. -/
structure Congr!.Config where
  /-- If `closePre := true`, then try to close goals before applying congruence lemmas
  using tactics such as `rfl` and `assumption.  These tactics are applied with the
  transparency level specified by `preTransparency`, which is `.reducible` by default. -/
  closePre : Bool := true
  /-- If `closePost := true`, then try to close goals that remain after no more congruence
  lemmas can be applied, using the same tactics as `closePre`. These tactics are applied
  with current tactic transparency level. -/
  closePost : Bool := true
  /-- The transparency level to use when applying a congruence theorem.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  transparency : TransparencyMode := TransparencyMode.reducible
  /-- The transparency level to use when trying to close goals before applying congruence lemmas.
  This includes trying to prove the goal by `rfl` and using the `assumption` tactic.
  By default this is `.reducible`, which prevents unfolding of most definitions. -/
  preTransparency : TransparencyMode := TransparencyMode.reducible
  /-- For passes that synthesize a congruence lemma using one side of the equality,
  we run the pass both for the left-hand side and the right-hand side. If `preferLHS` is `true`
  then we start with the left-hand side.

  This can be used to control which side's definitions are expanded when applying the
  congruence lemma (if `preferLHS = true` then the RHS can be expanded). -/
  preferLHS : Bool := true
  /-- Allow both sides to be partial applications.
  When false, given an equality `f a b = g x y z` this means we never consider
  proving `f a = g x y`.

  In this case, we might still consider `f = g x` if a pass generates a congruence lemma using the
  left-hand side. Use `sameFun := true` to ensure both sides are applications
  of the same function (making it be similar to the `congr` tactic). -/
  partialApp : Bool := true
  /-- Whether to require that both sides of an equality be applications of defeq functions.
  That is, if true, `f a = g x` is only considered if `f` and `g` are defeq (making it be similar
  to the `congr` tactic). -/
  sameFun : Bool := false
  /-- The maximum number of arguments to consider when doing congruence of function applications.
  For example, with `f a b c = g w x y z`, setting `maxArgs := some 2` means it will only consider
  either `f a b = g w x y` and `c = z` or `f a = g w x`, `b = y`, and `c = z`. Setting
  `maxArgs := none` (the default) means no limit.

  When the functions are dependent, `maxArgs` can prevent congruence from working at all.
  In `Fintype.card α = Fintype.card β`, one needs to have `maxArgs` at `2` or higher since
  there is a `Fintype` instance argument that depends on the first.

  When there aren't such dependency issues, setting `maxArgs := some 1` causes `congr!` to
  do congruence on a single argument at a time. This can be used in conjunction with the
  iteration limit to control exactly how many arguments are to be processed by congruence. -/
  maxArgs : Option Nat := none
  /-- For type arguments that are implicit or have forward dependencies, whether or not `congr!`
  should generate equalities even if the types do not look plausibly equal.

  We have a heuristic in the main congruence generator that types
  `α` and `β` are *plausibly equal* according to the following algorithm:

  - If the types are both propositions, they are plausibly equal (`Iff`s are plausible).
  - If the types are from different universes, they are not plausibly equal.
  - Suppose in whnf we have `α = f a₁ ... aₘ` and `β = g b₁ ... bₘ`. If `f` is not definitionally
    equal to `g` or `m ≠ n`, then `α` and `β` are not plausibly equal.
  - If there is some `i` such that `aᵢ` and `bᵢ` are not plausibly equal, then `α` and `β` are
    not plausibly equal.
  - Otherwise, `α` and `β` are plausibly equal.

  The purpose of this is to prevent considering equalities like `ℕ = ℤ` while allowing equalities
  such as `Fin n = Fin m` or `Subtype p = Subtype q` (so long as these are subtypes of the
  same type).

  The way this is implemented is that when the congruence generator is comparing arguments when
  looking at an equality of function applications, it marks a function parameter as "fixed" if the
  provided arguments are types that are not plausibly equal. The effect of this is that congruence
  succeeds only if those arguments are defeq at `transparency` transparency. -/
  typeEqs : Bool := false
  /-- As a last pass, perform eta expansion of both sides of an equality. For example,
  this transforms a bare `HAdd.hAdd` into `fun x y => x + y`. -/
  etaExpand : Bool := false
  /-- Whether to use the congruence generator that is used by `simp` and `congr`. This generator
  is more strict, and it does not respect all configuration settings. It does respect
  `preferLHS`, `partialApp` and `maxArgs` and transparency settings. It acts as if `sameFun := true`
  and it ignores `typeEqs`. -/
  useCongrSimp : Bool := false

/-- A configuration option that makes `congr!` do the sorts of aggressive unfoldings that `congr`
does while also similarly preventing `congr!` from considering partial applications or congruences
between different functions being applied. -/
def Congr!.Config.unfoldSameFun : Congr!.Config where
  partialApp := false
  sameFun := true
  transparency := .default
  preTransparency := .default

/-- Whether the given number of arguments is allowed to be considered. -/
def Congr!.Config.numArgsOk (config : Config) (numArgs : Nat) : Bool :=
  numArgs ≤ config.maxArgs.getD numArgs

/-- According to the configuration, how many of the arguments in `numArgs` should be considered. -/
def Congr!.Config.maxArgsFor (config : Config) (numArgs : Nat) : Nat :=
  min numArgs (config.maxArgs.getD numArgs)

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
    -- We don't want a unification specializing `Sort*` to `Prop`.
    let tgt ← withReducible mvarId.getType'
    let some (ty, _, _) := tgt.eq? | failure
    guard ty.isProp
    let [mvarId] ← mvarId.apply (mkConst ``propext []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to close the goal with using `proof_irrel_heq`. Returns whether or not it succeeds.

We need to be somewhat careful not to assign metavariables while doing this, otherwise we might
specialize `Sort*` to `Prop`.
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
Try to close the goal using `Subsingleton.elim`. Returns whether or not it succeeds.

We are careful to apply `Subsingleton.elim` in a way that does not assign any metavariables.
This is to prevent the `Subsingleton Prop` instance from being used as justification to specialize
`Sort*` to `Prop`.
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

For the purpose of generating nicer lemmas that have a better chance at something like
`to_additive` rewriting, this function supports generating lemmas where certain parameters
are meant to be fixed.

* If `fixedFun` is `false` (the default) then the lemma starts with three arguments for `f`, `f'`,
and `h : f = f'`. Otherwise, if `fixedFun` is `true` then the lemma starts with just `f`.

* If the `fixedParams` argument has `true` for a particular argument index, then this is a hint
that the congruence lemma may use the same parameter for both sides of the equality. There is
no guarantee -- it respects it if the types are equal for that parameter (i.e., if the parameter
does not depend on non-fixed parameters).
-/
partial def Congr!.mkHCongrThm (fType : Expr) (info : FunInfo)
    (fixedFun : Bool := false) (fixedParams : Array Bool := #[]) :
    MetaM (Expr × Expr) := do
  trace[congr!.synthesize] "ftype: {fType}"
  trace[congr!.synthesize] "deps: {info.paramInfo.map (fun p => p.backDeps)}"
  trace[congr!.synthesize] "fixedFun={fixedFun}, fixedParams={fixedParams}"
  doubleTelescope fType info.getArity fixedParams fun xs ys fixedParams => do
    trace[congr!.synthesize] "xs = {xs}"
    trace[congr!.synthesize] "ys = {ys}"
    trace[congr!.synthesize] "computed fixedParams={fixedParams}"
    let lctx := (← getLCtx) -- checkpoint of local context that only has parameters
    withLocalDeclD `f fType fun ef => withLocalDeclD `f' fType fun pef' => do
    let ef' := if fixedFun then ef else pef'
    withLocalDeclD `e (← mkEq ef ef') fun ee => do
    withNewEqs xs ys fixedParams fun eqs => do
      let fParams := if fixedFun then #[ef] else #[ef, ef', ee]
      let mut hs := fParams     -- parameters to the basic congruence lemma
      let mut hs' := fParams    -- parameters to the richer congruence lemma
      let mut vals' := fParams  -- how to calculate the basic parameters from the richer ones
      for i in [0 : info.getArity] do
        hs := hs.push xs[i]!
        hs' := hs'.push xs[i]!
        vals' := vals'.push xs[i]!
        if let some (eq, eq', val) := eqs[i]! then
          -- Not a fixed argument
          hs := hs.push ys[i]! |>.push eq
          hs' := hs'.push ys[i]! |>.push eq'
          vals' := vals'.push ys[i]! |>.push val
      -- Generate the theorem with respect to the simpler hypotheses
      let congrType ← mkForallFVars hs (← mkHEq (mkAppN ef xs) (mkAppN ef' ys))
      trace[congr!.synthesize] "simple congrType: {congrType}"
      let some proof ← withLCtx lctx (← getLocalInstances) <| trySolve congrType
        | throwError "Internal error when constructing congruence lemma proof"
      -- At this point, `mkLambdaFVars hs' (mkAppN proof vals')` is the richer proof.
      -- We try to precompute some of the arguments using `trySolve`.
      let mut hs'' := #[] -- eq' parameters that are actually used beyond those in `fParams`
      let mut pfVars := #[] -- eq' parameters that can be solved for already
      let mut pfVals := #[] -- the values to use for these parameters
      for i in [0 : info.getArity] do
        hs'' := hs''.push xs[i]!
        if let some (_, eq', _) := eqs[i]! then
          -- Not a fixed argument
          hs'' := hs''.push ys[i]!
          let pf? ← withLCtx lctx (← getLocalInstances) <| trySolve (← inferType eq')
          if let some pf := pf? then
            pfVars := pfVars.push eq'
            pfVals := pfVals.push pf
          else
            hs'' := hs''.push eq'
      -- Take `proof`, abstract the pfVars and provide the solved-for proofs (as an
      -- optimization for proof term size) then abstract the remaining variables.
      -- The `usedOnly` probably has no affect.
      -- Note that since we are doing `proof.beta vals'` there is technically some quadratic
      -- complexity, but it shouldn't be too bad since they're some applications of just variables.
      let proof' ← mkLambdaFVars fParams (← mkLambdaFVars (usedOnly := true) hs''
                    (mkAppN (← mkLambdaFVars pfVars (proof.beta vals')) pfVals))
      return (← inferType proof', proof')
where
  /-- Similar to doing `forallBoundedTelescope` twice, but makes use of the `fixed` array, which
  is used as a hint for whether both variables should be the same. This is only a hint though,
  since we respect it only if the binding domains are equal.
  We affix `'` to the second list of variables, and all the variables are introduced
  with default binder info. Calls `k` with the xs, ys, and a revised `fixed` array -/
  doubleTelescope {α} (fty : Expr) (numVars : Nat) (fixed : Array Bool)
      (k : Array Expr → Array Expr → Array Bool → MetaM α) : MetaM α := do
    let rec loop (i : Nat)
        (ftyx ftyy : Expr) (xs ys : Array Expr) (fixed' : Array Bool) : MetaM α := do
      if i < numVars then
        let ftyx ← whnf ftyx
        let ftyy ← whnf ftyy
        unless ftyx.isForall do
          throwError "doubleTelescope: function doesn't have enough parameters"
        withLocalDeclD ftyx.bindingName! ftyx.bindingDomain! fun fvarx => do
          let ftyx' := ftyx.bindingBody!.instantiate1 fvarx
          if fixed.getD i false && ftyx.bindingDomain! == ftyy.bindingDomain! then
            -- Fixed: use the same variable for both
            let ftyy' := ftyy.bindingBody!.instantiate1 fvarx
            loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvarx) (fixed'.push true)
          else
            -- Not fixed: use different variables
            let yname := ftyy.bindingName!.appendAfter "'"
            withLocalDeclD yname ftyy.bindingDomain! fun fvary => do
              let ftyy' := ftyy.bindingBody!.instantiate1 fvary
              loop (i + 1) ftyx' ftyy' (xs.push fvarx) (ys.push fvary) (fixed'.push false)
      else
        k xs ys fixed'
    loop 0 fty fty #[] #[] #[]
  /-- Introduce variables for equalities between the arrays of variables. Uses `fixedParams`
  to control whether to introduce an equality for each pair. The array of triples passed to `k`
  consists of (1) the simple congr lemma HEq arg, (2) the richer HEq arg, and (3) how to
  compute 1 in terms of 2. -/
  withNewEqs {α} (xs ys : Array Expr) (fixedParams : Array Bool)
      (k : Array (Option (Expr × Expr × Expr)) → MetaM α) : MetaM α :=
    let rec loop (i : Nat) (eqs : Array (Option (Expr × Expr × Expr))) := do
      if i < xs.size then
        let x := xs[i]!
        let y := ys[i]!
        if fixedParams[i]! then
          loop (i+1) (eqs.push none)
        else
          let deps := info.paramInfo[i]!.backDeps.filterMap (fun j => eqs[j]!)
          let eq' ← mkForallFVars (deps.map fun (eq, _, _) => eq) (← mkEqHEq x y)
          withLocalDeclD ((`e).appendIndexAfter (i+1)) (← mkEqHEq x y) fun h =>
          withLocalDeclD ((`e').appendIndexAfter (i+1)) eq' fun h' =>
            let v := mkAppN h' (deps.map fun (_, _, val) => val)
            loop (i+1) (eqs.push (h, h', v))
      else
        k eqs
    loop 0 #[]
  /-- Given a type that is a bunch of equalities implying a goal (for example, a basic
  congruence lemma), prove it if possible. Basic congruence lemmas should be provable by this.
  There are some extra tricks for handling arguments to richer congruence lemmas. -/
  trySolveCore (mvarId : MVarId) : MetaM Unit := do
    -- First cleanup the context since we're going to do `substEqs` and we don't want to
    -- accidentally use variables not actually used by the theorem.
    let mvarId ← mvarId.cleanup
    let (_, mvarId) ← mvarId.intros
    let mvarId := (← mvarId.substEqs).getD mvarId
    try mvarId.refl; return catch _ => pure ()
    try mvarId.hrefl; return catch _ => pure ()
    if ← mvarId.proofIrrelHeq then return
    -- Make the goal be an eq and then try `Subsingleton.elim`
    let mvarId ← mvarId.heqOfEq
    if ← mvarId.subsingletonElim then return
    -- We have no more tricks.
    throwError "was not able to solve for proof"
  trySolve (ty : Expr) : MetaM (Option Expr) := observing? do
    let mvar ← mkFreshExprMVar ty
    trace[congr!.synthesize] "trySolve {mvar.mvarId!}"
    -- The proofs we generate shouldn't require unfolding anything.
    withReducible <| trySolveCore mvar.mvarId!
    trace[congr!.synthesize] "trySolve success!"
    let pf ← instantiateMVars mvar
    return pf

/-- Returns whether or not it's reasonable to consider an equality between types `ty1` and `ty2`.
The heuristic is the following:

- If `ty1` and `ty2` are in `Prop`, then yes.
- If in whnf both `ty1` and `ty2` have the same head and if (recursively) it's reasonable to
  consider an equality between corresponding type arguments, then yes.
- Otherwise, no.

This helps keep congr from going too far and generating hypotheses like `ℝ = ℤ`.

To keep things from going out of control, there is a `maxDepth`. Additionally, if we do the check
with `maxDepth = 0` then the heuristic answers "no". -/
def Congr!.plausiblyEqualTypes (ty1 ty2 : Expr) (maxDepth : Nat := 5) : MetaM Bool :=
  match maxDepth with
  | 0 => return false
  | maxDepth + 1 => do
    -- Props are plausibly equal
    if (← isProp ty1) && (← isProp ty2) then
      return true
    -- Types from different type universes are not plausibly equal.
    -- This is redundant, but it saves carrying out the remaining checks.
    unless ← withNewMCtxDepth <| isDefEq (← inferType ty1) (← inferType ty2) do
      return false
    -- Now put the types into whnf, check they have the same head, and then recurse on arguments
    let ty1 ← whnfD ty1
    let ty2 ← whnfD ty2
    unless ← withNewMCtxDepth <| isDefEq ty1.getAppFn ty2.getAppFn do
      return false
    for arg1 in ty1.getAppArgs, arg2 in ty2.getAppArgs do
      if (← isType arg1) && (← isType arg2) then
        unless ← plausiblyEqualTypes arg1 arg2 maxDepth do
          return false
    return true

/--
This is like `Lean.MVarId.hcongr?` but (1) looks at both sides when generating the congruence lemma
and (2) inserts additional hypotheses from equalities from previous arguments.

It uses `Congr!.mkHCongrThm` to generate the congruence lemmas.

If the goal is an `Eq`, uses `eq_of_heq` first.

As a backup strategy, it uses the LHS/RHS method like in `Lean.MVarId.congrSimp?`
(where `Congr!.Config.preferLHS` determines which side to try first). This uses a particular side
of the target, generates the congruence lemma, then tries applying it. This can make progress
with higher transparency settings. To help the unifier, in this mode it assumes both sides have the
exact same function.
-/
partial
def Lean.MVarId.smartHCongr? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `congr!
    commitWhenSome? do
      let mvarId ← mvarId.eqOfHEq
      let some (_, lhs, _, rhs) := (← withReducible mvarId.getType').heq? | return none
      if let some mvars ← loop mvarId 0 lhs rhs [] [] then
        return mvars
      -- The "correct" behavior failed. However, it's often useful
      -- to apply congruence lemmas while unfolding definitions, which is what the
      -- basic `congr` tactic does due to limitations in how congruence lemmas are generated.
      -- We simulate this behavior here by generating congruence lemmas for the LHS and RHS and
      -- then applying them.
      trace[congr!] "Default smartHCongr? failed, trying LHS/RHS method"
      let (fst, snd) := if config.preferLHS then (lhs, rhs) else (rhs, lhs)
      if let some mvars ← forSide mvarId fst then
        return mvars
      else if let some mvars ← forSide mvarId snd then
        return mvars
      else
        return none
where
  loop (mvarId : MVarId) (numArgs : Nat) (lhs rhs : Expr) (lhsArgs rhsArgs : List Expr) :
      MetaM (Option (List MVarId)) :=
    match lhs.cleanupAnnotations, rhs.cleanupAnnotations with
    | .app f a, .app f' b => do
      if not (config.numArgsOk (numArgs + 1)) then
        return none
      let lhsArgs' := a :: lhsArgs
      let rhsArgs' := b :: rhsArgs
      -- We try to generate a theorem for the maximal number of arguments
      if let some mvars ← loop mvarId (numArgs + 1) f f' lhsArgs' rhsArgs' then
        return mvars
      -- That failing, we now try for the present number of arguments.
      if not config.partialApp && f.isApp && f'.isApp then
        -- It's a partial application on both sides though.
        return none
      -- The congruence generator only handles the case where both functions have
      -- definitionally equal types.
      unless ← withNewMCtxDepth <| isDefEq (← inferType f) (← inferType f') do
        return none
      let funDefEq ← withReducible <| withNewMCtxDepth <| isDefEq f f'
      if config.sameFun && not funDefEq then
        return none
      let info ← getFunInfoNArgs f (numArgs + 1)
      let mut fixed : Array Bool := #[]
      for larg in lhsArgs', rarg in rhsArgs', pinfo in info.paramInfo do
        if !config.typeEqs && (!pinfo.isExplicit || pinfo.hasFwdDeps) then
          -- When `typeEqs = false` then for non-explicit arguments or
          -- arguments with forward dependencies, we want type arguments
          -- to be plausibly equal.
          if ← isType larg then
            -- ^ since `f` and `f'` have defeq types, this implies `isType rarg`.
            unless ← Congr!.plausiblyEqualTypes larg rarg do
              fixed := fixed.push true
              continue
        fixed := fixed.push (← withReducible <| withNewMCtxDepth <| isDefEq larg rarg)
      let (congrThm, congrProof) ← Congr!.mkHCongrThm (← inferType f) info
                                    (fixedFun := funDefEq) (fixedParams := fixed)
      -- Now see if the congruence theorem actually applies in this situation by applying it!
      let (congrThm', congrProof') :=
        if funDefEq then
          (congrThm.bindingBody!.instantiate1 f, congrProof.beta #[f])
        else
          (congrThm.bindingBody!.bindingBody!.instantiateRev #[f, f'],
           congrProof.beta #[f, f'])
      observing? <| applyCongrThm? config mvarId congrThm' congrProof'
    | _, _ => return none
  forSide (mvarId : MVarId) (side : Expr) : MetaM (Option (List MVarId)) := do
    let side := side.cleanupAnnotations
    if not side.isApp then return none
    let numArgs := config.maxArgsFor side.getAppNumArgs
    if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
    let mut f := side
    for _ in [:numArgs] do
      f := f.appFn!'
    let info ← getFunInfoNArgs f numArgs
    let mut fixed : Array Bool := #[]
    if !config.typeEqs then
      -- We need some strategy for fixed parameters to keep `forSide` from applying
      -- in cases where `Congr!.possiblyEqualTypes` suggested not to in the previous pass.
      for pinfo in info.paramInfo, arg in side.getAppArgs do
        if pinfo.isProp || !(← isType arg) then
          fixed := fixed.push false
        else if pinfo.isExplicit && !pinfo.hasFwdDeps then
          -- It's fine generating equalities for explicit type arguments without forward
          -- dependencies. Only allowing these is a little strict, because an argument
          -- might be something like `Fin n`. We might consider being able to generate
          -- congruence lemmas that only allow equalities where they can plausibly go,
          -- but that would take looking at a whole application tree.
          fixed := fixed.push false
        else
          fixed := fixed.push true
    let (congrThm, congrProof) ←
      Congr!.mkHCongrThm (← inferType f) info (fixedFun := true) (fixedParams := fixed)
    let congrThm' := congrThm.bindingBody!.instantiate1 f
    let congrProof' := congrProof.beta #[f]
    observing? <| applyCongrThm? config mvarId congrThm' congrProof'

/--
Like `Lean.MVarId.congr?` but instead of using only the congruence lemma associated to the LHS,
it tries the RHS too, in the order specified by `config.preferLHS`.

It uses `Lean.Meta.mkCongrSimp?` to generate a congruence lemma, like in the `congr` tactic.

Applies the congruence generated congruence lemmas according to `config`.
-/
def Lean.MVarId.congrSimp? (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) :=
  mvarId.withContext do
    unless config.useCongrSimp do return none
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
      let numArgs := config.maxArgsFor side.getAppNumArgs
      if not config.partialApp && numArgs < side.getAppNumArgs then
        return none
      let mut f := side
      for _ in [:numArgs] do
        f := f.appFn!'
      let some congrThm ← mkCongrSimpNArgs f numArgs
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
def Lean.MVarId.userCongr? (config : Congr!.Config) (mvarId : MVarId) :
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

/-- Like `implies_congr` but provides an additional assumption to the second hypothesis.
This is a non-dependent version of `pi_congr` that allows the domains to be different. -/
private theorem implies_congr' {α α' : Sort u} {β β' : Sort v} (h : α = α') (h' : α' → β = β') :
    (α → β) = (α' → β') := by
  cases h
  show (∀ (x : α), (fun _ => β) x) = _
  rw [funext h']

/-- A version of `Lean.MVarId.congrImplies?` that uses `implies_congr'`
instead of `implies_congr`. -/
def Lean.MVarId.congrImplies?' (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  observing? do
    let [mvarId₁, mvarId₂] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr')
      | throwError "unexpected number of goals"
    return [mvarId₁, mvarId₂]

/--
Try to apply `Subsingleton.helim` if the goal is a `HEq`. Tries synthesizing a `Subsingleton`
instance for both the LHS and the RHS.

If successful, this reduces proving `@HEq α x β y` to proving `α = β`.
-/
def Lean.MVarId.subsingletonHelim? (mvarId : MVarId) : MetaM (Option (List MVarId)) :=
  mvarId.withContext <| observing? do
    mvarId.checkNotAssigned `subsingletonHelim
    let some (α, lhs, β, rhs) := (← withReducible mvarId.getType').heq? | failure
    let eqmvar ← mkFreshExprSyntheticOpaqueMVar (← mkEq α β) (← mvarId.getTag)
    -- First try synthesizing using the left-hand side for the Subsingleton instance
    if let some pf ← observing? (mkAppM ``Subsingleton.helim #[eqmvar, lhs, rhs]) then
      mvarId.assign pf
      return [eqmvar.mvarId!]
    let eqsymm ← mkAppM ``Eq.symm #[eqmvar]
    -- Second try synthesizing using the right-hand side for the Subsingleton instance
    if let some pf ← observing? (mkAppM ``Subsingleton.helim #[eqsymm, rhs, lhs]) then
      mvarId.assign (← mkAppM ``HEq.symm #[pf])
      return [eqmvar.mvarId!]
    failure

/--
A list of all the congruence strategies used by `Lean.MVarId.congrCore!`.
-/
def Lean.MVarId.congrPasses! :
    List (String × (Congr!.Config → MVarId → MetaM (Option (List MVarId)))) :=
  [("user congr", userCongr?),
   ("hcongr lemma", smartHCongr?),
   ("congr simp lemma", congrSimp?),
   ("Subsingleton.helim", fun _ => subsingletonHelim?),
   ("obvious funext", fun _ => obviousFunext?),
   ("obvious hfunext", fun _ => obviousHfunext?),
   ("congr_implies", fun _ => congrImplies?'),
   ("congr_pi", fun _ => congrPi?)]

structure CongrState where
  /-- Accumulated goals that `congr!` could not handle. -/
  goals : Array MVarId
  /-- Patterns to use when doing intro. -/
  patterns : List (TSyntax `rcasesPat)

abbrev CongrMetaM := StateRefT CongrState MetaM

/-- Pop the next pattern from the current state. -/
def CongrMetaM.nextPattern : CongrMetaM (Option (TSyntax `rcasesPat)) := do
  modifyGet fun s =>
    if let p :: ps := s.patterns then
      (p, {s with patterns := ps})
    else
      (none, s)

private theorem heq_imp_of_eq_imp {p : HEq x y → Prop} (h : (he : x = y) → p (heq_of_eq he))
    (he : HEq x y) : p he := by
  cases he
  exact h rfl

private theorem eq_imp_of_iff_imp {p : x = y → Prop} (h : (he : x ↔ y) → p (propext he))
    (he : x = y) : p he := by
  cases he
  exact h Iff.rfl

/--
Does `Lean.MVarId.intros` but then cleans up the introduced hypotheses, removing anything
that is trivial. If there are any patterns in the current `CongrMetaM` state then instead
of `Lean.MVarId.intros` it does `Std.Tactic.RCases.rintro`.

Cleaning up includes:
- deleting hypotheses of the form `HEq x x`, `x = x`, and `x ↔ x`.
- deleting Prop hypotheses that are already in the local context.
- converting `HEq x y` to `x = y` if possible.
- converting `x = y` to `x ↔ y` if possible.
-/
partial
def Lean.MVarId.introsClean (mvarId : MVarId) : CongrMetaM (List MVarId) :=
  loop mvarId
where
  heqImpOfEqImp (mvarId : MVarId) : MetaM (Option MVarId) :=
    observing? <| withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``heq_imp_of_eq_imp) | failure
      return mvarId
  eqImpOfIffImp (mvarId : MVarId) : MetaM (Option MVarId) :=
    observing? <| withReducible do
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``eq_imp_of_iff_imp) | failure
      return mvarId
  loop (mvarId : MVarId) : CongrMetaM (List MVarId) :=
    mvarId.withContext do
      let ty ← withReducible <| mvarId.getType'
      if ty.isForall then
        let mvarId := (← heqImpOfEqImp mvarId).getD mvarId
        let mvarId := (← eqImpOfIffImp mvarId).getD mvarId
        let ty ← withReducible <| mvarId.getType'
        if ty.isArrow then
          if ← (isTrivialType ty.bindingDomain!
                <||> (← getLCtx).anyM (fun decl => do
                        return (← instantiateMVars decl.type) == ty.bindingDomain!)) then
            -- Don't intro, clear it
            let mvar ← mkFreshExprSyntheticOpaqueMVar ty.bindingBody! (← mvarId.getTag)
            mvarId.assign <| .lam .anonymous ty.bindingDomain! mvar .default
            return ← loop mvar.mvarId!
        if let some patt ← CongrMetaM.nextPattern then
          let gs ← Term.TermElabM.run' <| Std.Tactic.RCases.rintro #[patt] none mvarId
          List.join <$> gs.mapM loop
        else
          let (_, mvarId) ← mvarId.intro1
          loop mvarId
      else
        return [mvarId]
  isTrivialType (ty : Expr) : MetaM Bool := do
    unless ← Meta.isProp ty do
      return false
    let ty ← instantiateMVars ty
    if let some (lhs, rhs) := ty.eqOrIff? then
      if lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    if let some (α, lhs, β, rhs) := ty.heq? then
      if α.cleanupAnnotations == β.cleanupAnnotations
          && lhs.cleanupAnnotations == rhs.cleanupAnnotations then
        return true
    return false

/-- Convert a goal into an `Eq` goal if possible (since we have a better shot at those).
Also, if `tryClose := true`, then try to close the goal using an assumption, `Subsingleton.Elim`,
or definitional equality. -/
def Lean.MVarId.preCongr! (mvarId : MVarId) (tryClose : Bool) : MetaM (Option MVarId) := do
  -- Next, turn `HEq` and `Iff` into `Eq`
  let mvarId ← mvarId.heqOfEq
  if tryClose then
    -- This is a good time to check whether we have a relevant hypothesis.
    if ← mvarId.assumptionCore then return none
  let mvarId ← mvarId.iffOfEq
  if tryClose then
    -- Now try definitional equality. No need to try `mvarId.hrefl` since we already did `heqOfEq`.
    -- We allow synthetic opaque metavariables to be assigned to fill in `x = _` goals that might
    -- appear (for example, due to using `convert` with placeholders).
    try withAssignableSyntheticOpaque mvarId.refl; return none catch _ => pure ()
    -- Now we go for (heterogenous) equality via subsingleton considerations
    if ← mvarId.subsingletonElim then return none
    if ← mvarId.proofIrrelHeq then return none
  return some mvarId

def Lean.MVarId.congrCore! (config : Congr!.Config) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  mvarId.checkNotAssigned `congr!
  let s ← saveState
  /- We do `liftReflToEq` here rather than in `preCongr!` since we don't want to commit to it
     if there are no relevant congr lemmas. -/
  let mvarId ← mvarId.liftReflToEq
  for (passName, pass) in congrPasses! do
    try
      if let some mvarIds ← pass config mvarId then
        trace[congr!] "pass succeeded: {passName}"
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
def Lean.MVarId.postCongr! (config : Congr!.Config) (mvarId : MVarId) : MetaM (Option MVarId) := do
  let some mvarId ← mvarId.preCongr! config.closePost | return none
  -- Convert `p = q` to `p ↔ q`, which is likely the more useful form:
  let mvarId ← mvarId.propext
  if config.closePost then
    -- `preCongr` sees `p = q`, but now we've put it back into `p ↔ q` form.
    if ← mvarId.assumptionCore then return none
  if config.etaExpand then
    if let some (_, lhs, rhs) := (← withReducible mvarId.getType').eq? then
      let lhs' ← Meta.etaExpand lhs
      let rhs' ← Meta.etaExpand rhs
      return ← mvarId.change (← mkEq lhs' rhs')
  return mvarId

/-- A more insistent version of `Lean.MVarId.congrN`.
See the documentation on the `congr!` syntax.

The `depth?` argument controls the depth of the recursion. If `none`, then it uses a reasonably
large bound that is linear in the expression depth. -/
def Lean.MVarId.congrN! (mvarId : MVarId)
    (depth? : Option Nat := none) (config : Congr!.Config := {})
    (patterns : List (TSyntax `rcasesPat) := []) :
    MetaM (List MVarId) := do
  let ty ← withReducible <| mvarId.getType'
  -- A reasonably large yet practically bounded default recursion depth.
  let defaultDepth := min 1000000 (8 * (1 + ty.approxDepth.toNat))
  let depth := depth?.getD defaultDepth
  let (_, s) ← go depth depth mvarId |>.run {goals := #[], patterns := patterns}
  return s.goals.toList
where
  post (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
      if let some mvarId ← mvarId.postCongr! config then
        modify (fun s => {s with goals := s.goals.push mvarId})
      else
        trace[congr!] "Dispatched goal by post-processing step."
  go (depth : Nat) (n : Nat) (mvarId : MVarId) : CongrMetaM Unit := do
    for mvarId in ← mvarId.introsClean do
      if let some mvarId ← withTransparency config.preTransparency <|
                              mvarId.preCongr! config.closePre then
        match n with
          | 0 =>
            trace[congr!] "At level {depth - n}, doing post-processing. {mvarId}"
            post mvarId
          | n + 1 =>
            trace[congr!] "At level {depth - n}, trying congrCore!. {mvarId}"
            if let some mvarIds ← mvarId.congrCore! config then
              mvarIds.forM (go depth n)
            else
              post mvarId

namespace Congr!

declare_config_elab elabConfig Config

/--
Equates pieces of the left-hand side of a goal to corresponding pieces of the right-hand side by
recursively applying congruence lemmas. For example, with `⊢ f as = g bs` we could get
two goals `⊢ f = g` and `⊢ as = bs`.

Syntax:
```
congr!
congr! n
congr! with x y z
congr! n with x y z
```
Here, `n` is a natural number and `x`, `y`, `z` are `rintro` patterns (like `h`, `rfl`, `⟨x, y⟩`,
`_`, `-`, `(h | h)`, etc.).

The `congr!` tactic is similar to `congr` but is more insistent in trying to equate left-hand sides
to right-hand sides of goals. Here is a list of things it can try:

- If `R` in `⊢ R x y` is a reflexive relation, it will convert the goal to `⊢ x = y` if possible.
  The list of reflexive relations is maintained using the `@[refl]` attribute.
  As a special case, `⊢ p ↔ q` is converted to `⊢ p = q` during congruence processing and then
  returned to `⊢ p ↔ q` form at the end.

- If there is a user congruence lemma associated to the goal (for instance, a `@[congr]`-tagged
  lemma applying to `⊢ List.map f xs = List.map g ys`), then it will use that.

- It uses a congruence lemma generator at least as capable as the one used by `congr` and `simp`.
  If there is a subexpression that can be rewritten by `simp`, then `congr!` should be able
  to generate an equality for it.

- It can do congruences of pi types using lemmas like `implies_congr` and `pi_congr`.

- Before applying congruences, it will run the `intros` tactic automatically.
  The introduced variables can be given names using a `with` clause.
  This helps when congruence lemmas provide additional assumptions in hypotheses.

- When there is an equality between functions, so long as at least one is obviously a lambda, we
  apply `funext` or `Function.hfunext`, which allows for congruence of lambda bodies.

- It can try to close goals using a few strategies, including checking
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
This overrides the default, which is to apply congruence lemmas at reducible transparency.

The `congr!` tactic is aggressive with equating two sides of everything. There is a predefined
configuration that uses a different strategy:
Try
```lean
congr! (config := .unfoldSameFun)
```
This only allows congruences between functions applications of definitionally equal functions,
and it applies congruence lemmas at default transparency (rather than just reducible).
This is somewhat like `congr`.

See `Congr!.Config` for all options.
-/
syntax (name := congr!) "congr!" (Parser.Tactic.config)? (ppSpace num)?
  (" with" (ppSpace colGt rintroPat)*)? : tactic

elab_rules : tactic
| `(tactic| congr! $[$cfg:config]? $[$n]? $[with $ps?*]?) => do
  let config ← elabConfig (mkOptionalNode cfg)
  let patterns := (Std.Tactic.RCases.expandRIntroPats (ps?.getD #[])).toList
  liftMetaTactic fun g ↦
    let depth := n.map (·.getNat)
    g.congrN! depth config patterns

end Congr!
