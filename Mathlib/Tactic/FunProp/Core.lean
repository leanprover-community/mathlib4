/-
Copyright (c) 2024 Tomáš Skřivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomáš Skřivan
-/
module

public meta import Mathlib.Tactic.FunProp.Theorems
public meta import Mathlib.Tactic.FunProp.ToBatteries
public meta import Mathlib.Tactic.FunProp.Types
public meta import Mathlib.Lean.Expr.Basic
public import Batteries.Tactic.Exact
public import Mathlib.Tactic.FunProp.Theorems
public import Qq

/-!
# Tactic `fun_prop` for proving function properties like `Continuous f`, `Differentiable ℝ f`, ...
-/

public meta section

namespace Mathlib
open Lean Meta Qq

namespace Meta.FunProp


/-- Synthesize instance of type `type` and
  1. assign it to `x` if `x` is meta variable
  2. check it is equal to `x` -/
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | .some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
synthesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fun_prop]
      "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false



/-- Synthesize arguments `xs` either with typeclass synthesis, with `fun_prop` or with
discharger. -/
def synthesizeArgs (thmId : Origin) (xs : Array Expr) :
    FunPropM Bool := do
  let mut postponed : Array Expr := #[]
  for x in xs do
    let type ← inferType x
    if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue
      else if (← isFunPropGoal type) then
        -- try function property
        if let some r ← funProp type then
          if (← isDefEq x r.proof) then
            continue
          else do
            trace[Meta.Tactic.fun_prop]
              "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return false
      else
        -- try user provided discharger
        let ctx : Context ← read
        if (← isProp type) then
          if let some proof ← ctx.disch type then
            if (← isDefEq x proof) then
              continue
            else do
              trace[Meta.Tactic.fun_prop]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false
          else
            logError s!"Failed to prove necessary assumption `{← ppExpr type}` \
                        when applying theorem `{← ppOrigin' thmId}`."

      if ¬(← isProp type) then
        postponed := postponed.push x
        continue
      else
        trace[Meta.Tactic.fun_prop]
          "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
        return false

  for x in postponed do
    if (← instantiateMVars x).isMVar then
      logError s!"Failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})` \
      when applying theorem `{← ppOrigin' thmId}`."

      trace[Meta.Tactic.fun_prop]
        "{← ppOrigin thmId}, failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})`"
      return false

  return true


/-- Try to apply theorem - core function -/
def tryTheoremCore (xs : Array Expr) (val : Expr) (type : Expr) (goal : Goal)
    (thmId : Origin) : FunPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => return s!"applying: {← ppOrigin' thmId}") do

  let e ← goal.mkFreshExpr

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    return some { proof := proof }
  else
    trace[Meta.Tactic.fun_prop] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


/-- Try to apply a theorem provided some of the theorem arguments. -/
def tryTheoremWithHint? (goal : Goal) (thmOrigin : Origin)
    (hint : Array (Nat × Expr)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    let type ← inferType thmProof
    let (xs, _, type) ← forallMetaTelescope type

    for (i,x) in hint do
      try
        for (id,v) in hint do
          xs[id]!.mvarId!.assignIfDefEq v
      catch _ =>
        trace[Debug.Meta.Tactic.fun_prop]
          "failed to use hint {i} `{← ppExpr x} when applying theorem {← ppOrigin thmOrigin}"

    tryTheoremCore xs thmProof type goal thmOrigin

  -- `simp` introduces new meta variable context depth for some reason
  -- This is probably to avoid mvar assignment when trying a theorem fails
  --
  -- However, in `fun_prop` case this is not completely desirable
  -- For example, I want to be able to solve a goal with mvars like `ContDiff ℝ ?n f` using local
  -- hypothesis `(h : ContDiff ℝ ∞ f)` and assign `∞` to the mvar `?n`.
  --
  -- This could be problematic if there are two local hypothesis `(hinf : ContDiff ℝ ∞ f)` and
  -- `(h1 : ContDiff ℝ 1 f)` and apart from solving `ContDiff ℝ ?n f` there is also a subgoal
  -- `2 ≤ ?n`. If `fun_prop` decides to try `h1` first it would assign `1` to `?n` and then there
  -- is no hope solving `2 ≤ 1` and it won't be able to apply `hinf` after trying `h1` as `n?` is
  -- assigned already. Ideally `fun_prop` would roll back the `MetaM.State`. This issue did not
  -- come up yet so I didn't bother and I'm worried about the performance impact.
  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go


/-- Try to apply a theorem `thmOrigin` to the goal `e`. -/
def tryTheorem? (goal : Goal) (thmOrigin : Origin)
    (newMCtxDepth : Bool := false) : FunPropM (Option Result) :=
  tryTheoremWithHint? goal thmOrigin #[] newMCtxDepth


/--
Try to prove `e` using the *identity lambda theorem*.

For example, `e = q(Continuous fun x ↦ x)` and `funPropDecl` is `FunPropDecl` for `Continuous`.
-/
def applyIdRule (goal : Goal) : FunPropM (Option Result) := do
  let thms ← getLambdaTheorems goal.decl.funPropName .id
  if thms.size = 0 then
    let msg := s!"missing identity rule to prove `{← goal.pp'}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? goal (.decl thm.thmName) #[] then
      return r

  return none

/--
Try to prove `e` using the *constant lambda theorem*.

For example, `e = q(Continuous fun x ↦ y)` and `funPropDecl` is `FunPropDecl` for `Continuous`.
-/
def applyConstRule (goal : Goal) :
    FunPropM (Option Result) := do
  let thms ← getLambdaTheorems goal.decl.funPropName .const
  if thms.size = 0 then
    let msg := s!"missing constant rule to prove `{← goal.pp'}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none
  for thm in thms do
    let .const := thm.thmArgs | return none
    if let some r ← tryTheorem? goal (.decl thm.thmName) then
      return r

  return none

/--
Try to prove `e` using the *apply lambda theorem*.

For example, `e = q(Continuous fun f ↦ f x)` and `funPropDecl` is `FunPropDecl` for `Continuous`.
-/
def applyApplyRule (goal : Goal) : FunPropM (Option Result) := do
  let thms := (← getLambdaTheorems goal.decl.funPropName .apply)
  for thm in thms do
    if let some r ← tryTheoremWithHint? goal (.decl thm.thmName) #[] then
      return r

  return none

/--
Try to prove `e` using *composition lambda theorem*.

For example, `e = q(Continuous fun x ↦ f (g x))` and `funPropDecl` is `FunPropDecl` for
`Continuous`

You also have to provide the functions `f` and `g`. -/
def applyCompRule (goal : Goal) (f g : Expr) : FunPropM (Option Result) := do

  let thms ← getLambdaTheorems goal.decl.funPropName .comp
  if thms.size = 0 then
    let msg := s!"missing composition rule to prove `{← goal.pp'}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | return none
    if let some r ← tryTheoremWithHint? goal (.decl thm.thmName) #[(id_f, f), (id_g, g)] then
      return r

  return none

/--
Try to prove `e` using *pi lambda theorem*.

For example, `e = q(Continuous fun x y ↦ f x y)` and `funPropDecl` is `FunPropDecl` for
`Continuous`
-/
def applyPiRule (goal : Goal) : FunPropM (Option Result) := do

  let thms ← getLambdaTheorems goal.decl.funPropName .pi
  if thms.size = 0 then
    let msg := s!"missing pi rule to prove `{← goal.pp'}`"
    logError msg
    trace[Meta.Tactic.fun_prop] msg
    return none

  for thm in thms do
    if let some r ← tryTheoremWithHint? goal (.decl thm.thmName) #[] then
      return r

  return none


/--
Try to prove `e = q(P (fun x ↦ let y := φ x; ψ x y)`.

For example,
  - `funPropDecl` is `FunPropDecl` for `Continuous`
  - `e = q(Continuous fun x ↦ let y := φ x; ψ x y)`
  - `f = q(fun x ↦ let y := φ x; ψ x y)`
-/
def letCase (goal : Goal) (f : Expr) :
    FunPropM (Option Result) := do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType  := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody  := yBody.consumeMData
    -- We perform reduction because the type is quite often of the form
    -- `(fun x ↦ Y) #0` which is just `Y`
    -- Usually this is caused by the usage of `FunLike`
    let yType := yType.headBeta
    if (yType.hasLooseBVar 0) then
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

    -- let binding can be pulled out of the lambda function
    if ¬(yValue.hasLooseBVar 0) then
      let body := yBody.swapBVars 0 1
      let e ← goal.mkFreshExpr
      let e' := mkLet yName yType yValue
        (e.setArg (goal.decl.funArgId) (.lam xName xType body xBi))
      return ← funProp e'

    match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
    | true, true =>
      let f ← mkUncurryFun 2 (Expr.lam xName xType (.lam yName yType yBody default) xBi)
      let g := Expr.lam xName xType (binderInfo := default)
        (mkAppN (← mkConstWithFreshMVarLevels ``Prod.mk) #[xType,yType,.bvar 0, yValue])
      applyCompRule goal f g

    | true, false =>
      let f := Expr.lam yName yType yBody default
      let g := Expr.lam xName xType yValue default
      applyCompRule goal f g

    | false, _ =>
      let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
      let e ← goal.mkFreshExpr
      funProp (e.setArg (goal.decl.funArgId) f)

  | _ => throwError "expected expression of the form `fun x ↦ lam y := ..; ..`"


/-- Prove function property of using *morphism theorems*. -/
def applyMorRules (goal : Goal) (fData : FunctionData) :
    FunPropM (Option Result) := do
  trace[Debug.Meta.Tactic.fun_prop]
    "applying morphism theorems to {← goal.pp}"

  match ← fData.isMorApplication with
  | .none => throwError
    "fun_prop bug: invalid use of mor rules on {← goal.pp}"
  | .underApplied =>
    applyPiRule goal
  | .overApplied =>
    let some (f, g) ← fData.peeloffArgDecomposition | return none
    applyCompRule goal f g
  | .exact =>

    let candidates ← getMorphismTheorems (← goal.mkFreshExpr)

    trace[Meta.Tactic.fun_prop]
      "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

    for c in candidates do
      if let some r ← tryTheorem? goal (.decl c.thmName) then
        return r

    trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
    return none

/-- Prove function property of using *transition theorems*. -/
def applyTransitionRules (goal : Goal) :
    FunPropM (Option Result) := do
  withIncreasedTransitionDepth do

  let candidates ← getTransitionTheorems (← goal.mkFreshExpr)

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  for c in candidates do
    if let some r ← tryTheorem? goal (.decl c.thmName) then
      return r

  trace[Debug.Meta.Tactic.fun_prop] "no theorem matched"
  return none

/-- Try to remove applied argument i.e. prove `P (fun x ↦ f x y)` from `P (fun x ↦ f x)`.

For example
  - `funPropDecl` is `FunPropDecl` for `Continuous`
  - `e = q(Continuous fun x ↦ foo (bar x) y)`
  - `fData` contains info on `fun x ↦ foo (bar x) y`
  This tries to prove `Continuous fun x ↦ foo (bar x) y` from `Continuous fun x ↦ foo (bar x)`
-/
def removeArgRule (goal : Goal) (fData : FunctionData) :
    FunPropM (Option Result) := do

  match h : fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr (← goal.mkFreshExpr)}"
  | n + 1 =>
    let arg := fData.args[n]

    if arg.coe.isSome then
      -- if have to apply morphisms rules if we deal with morphisms
      return ← applyMorRules goal fData
    else
      let some (f, g) ← fData.peeloffArgDecomposition | return none
      applyCompRule goal f g


/-- Prove function property of `fun f ↦ f x₁ ... xₙ`. -/
def bvarAppCase (goal : Goal) (fData : FunctionData) :
    FunPropM (Option Result) := do

  if (← fData.isMorApplication) != .none then
    applyMorRules goal fData
  else
    if let some (f, g) ← fData.nontrivialDecomposition then
      applyCompRule goal f g
    else
      applyApplyRule goal

/--
Get candidate theorems from the environment for function property `funPropDecl` and
function `funName`. -/
def getDeclTheorems (funPropDecl : FunPropDecl) (funName : Name)
    (mainArgs : Array Nat) (appliedArgs : Nat) : MetaM (Array FunctionTheorem) := do

  let thms ← getTheoremsForFunction funName funPropDecl.funPropName

  let thms := thms
    |>.filter (fun thm => (isOrderedSubsetOf mainArgs thm.mainArgs))
    |>.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)
  -- todo: sorting and filtering
  return thms

/--
Get candidate theorems from the local context for function property `funPropDecl` and
function `funName`. -/
def getLocalTheorems (funPropDecl : FunPropDecl) (funOrigin : Origin)
    (mainArgs : Array Nat) (appliedArgs : Nat) : FunPropM (Array FunctionTheorem) := do

  let mut thms : Array FunctionTheorem := #[]
  let lctx ← getLCtx
  for var in lctx do
    if (var.kind = Lean.LocalDeclKind.auxDecl) then
      continue
    let type ← instantiateMVars var.type
    let thm? : Option FunctionTheorem ←
      forallTelescope type fun _ b => do
      let b ← whnfR b
      let some (decl, f) ← getFunProp? b | return none
      unless decl.funPropName = funPropDecl.funPropName do return none

      let .data fData ← getFunctionData? f (← unfoldNamePred)
        | return none
      unless (fData.getFnOrigin == funOrigin) do return none

      unless isOrderedSubsetOf mainArgs fData.mainArgs do return none

      let dec? ← fData.nontrivialDecomposition

      let thm : FunctionTheorem := {
        funPropName := funPropDecl.funPropName
        thmOrigin := .fvar var.fvarId
        funOrigin := funOrigin
        mainArgs := fData.mainArgs
        appliedArgs := fData.args.size
        priority := eval_prio default
        form := if dec?.isSome then .comp else .uncurried
      }

      return some thm

    if let some thm := thm? then
      thms := thms.push thm

  thms := thms
    |>.qsort (fun t s =>
      let dt := (Int.ofNat t.appliedArgs - Int.ofNat appliedArgs).natAbs
      let ds := (Int.ofNat s.appliedArgs - Int.ofNat appliedArgs).natAbs
      match compare dt ds with
      | .lt => true
      | .gt => false
      | .eq => t.mainArgs.size < s.mainArgs.size)

  return thms


/-- Try to apply *function theorems* `thms` to `e`. -/
def tryTheorems (goal : Goal) (fData : FunctionData)
    (thms : Array FunctionTheorem) :
    FunPropM (Option Result) := do

  -- none - decomposition not tried
  -- some none - decomposition failed
  -- some some (f, g) - successful decomposition
  let mut dec? : Option (Option (Expr × Expr)) := none

  for thm in thms do

    trace[Debug.Meta.Tactic.fun_prop] s!"trying theorem {← ppOrigin' thm.thmOrigin}"

    match compare thm.appliedArgs fData.args.size with
    | .lt =>
      trace[Meta.Tactic.fun_prop] s!"removing argument to later use {← ppOrigin' thm.thmOrigin}"
      if let some r ← removeArgRule goal fData then
        return r
      continue
    | .gt =>
      trace[Meta.Tactic.fun_prop] s!"adding argument to later use {← ppOrigin' thm.thmOrigin}"
      if let some r ← applyPiRule goal then
        return r
      continue
    | .eq =>
      if thm.form == .comp then
        if let some r ← tryTheorem? goal thm.thmOrigin then
          return r
      else

        if thm.mainArgs.size == fData.mainArgs.size then
          if dec?.isNone then
            dec? := some (← fData.nontrivialDecomposition)
          match dec? with
          | some none =>
            if let some r ← tryTheorem? goal thm.thmOrigin then
              return r
          | some (some (f, g)) =>
            trace[Meta.Tactic.fun_prop]
              s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                   ({← ppExpr f}) ∘ ({← ppExpr g})"
            if let some r ← applyCompRule goal f g then
              return r
          | _ => continue
        else
          let some (f, g) ← fData.decompositionOverArgs thm.mainArgs | continue
          trace[Meta.Tactic.fun_prop]
            s!"decomposing to later use {←ppOrigin' thm.thmOrigin} as:
                 ({← ppExpr f}) ∘ ({← ppExpr g})"
          if let some r ← applyCompRule goal f g then
            return r
      -- todo: decompose if uncurried and arguments do not match exactly
  return none

/-- Prove function property of `fun x ↦ f x₁ ... xₙ` where `f` is free variable. -/
def fvarAppCase (goal : Goal) (fData : FunctionData) :
    FunPropM (Option Result) := do

  -- fvar theorems are almost exclusively in uncurried form so we decompose if we can
  if let some (f, g) ← fData.nontrivialDecomposition then
    applyCompRule goal f g
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalTheorems goal.decl (.fvar id) fData.mainArgs fData.args.size
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {←ppExpr (.fvar id)} \
         {← thms.mapM fun thm => ppOrigin' thm.thmOrigin}"

    if let some r ← tryTheorems goal fData thms then
      return r

    if let some f ← fData.unfoldHeadFVar? then
      trace[Meta.Tactic.fun_prop] m!"unfolded local function {fData.fn}, {goal.mainFun} ==> {f}"
      let goal' ← goal.updateMainFun f
      if let some r ← funProp (← goal'.mkFreshExpr).2 then
        return r

    if (← fData.isMorApplication) != .none then
      if let some r ← applyMorRules goal fData then
        return r

    if (← fData.nontrivialDecomposition).isNone then
      if let some r ← applyTransitionRules goal then
        return r

    if thms.size = 0 then
      logError s!"No theorems found for `{← ppExpr (.fvar id)}` in order to prove \
                  `{← goal.pp'}`"

    return none


/-- Prove function property of `fun x ↦ f x₁ ... xₙ` where `f` is declared function. -/
def constAppCase (goal : Goal) (fData : FunctionData) :
    FunPropM (Option Result) := do

  let some (funName, _) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems goal.decl funName fData.mainArgs fData.args.size

  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppOrigin' thm.thmOrigin}"

  if let some r ← tryTheorems goal fData globalThms then
    return r

  -- Try local theorems - this is useful for recursive functions
  let localThms ← getLocalTheorems goal.decl (.decl funName) fData.mainArgs fData.args.size
  if localThms.size ≠ 0 then
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {funName} \
        {← localThms.mapM fun thm => ppOrigin' thm.thmOrigin}"
  if let some r ← tryTheorems goal fData localThms then
    return r

  -- log error if no global or local theorems were found
  if globalThms.size = 0 && localThms.size = 0 then
     logError s!"No theorems found for `{funName}` in order to prove \
                 `{← goal.pp'}`"

  if (← fData.isMorApplication) != .none then
    if let some r ← applyMorRules goal fData then
      return r

  if let some (f, g) ← fData.nontrivialDecomposition then
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{goal.decl.funPropName}` theorems for `{funName}`
         trying again after decomposing function as: `({← ppExpr f}) ∘ ({← ppExpr g})`"

    if let some r ← applyCompRule goal f g then
      return r
  else
    trace[Meta.Tactic.fun_prop]
      s!"failed applying `{goal.decl.funPropName}` theorems for `{funName}`
         now trying to prove `{goal.decl.funPropName}` from another function property"

    if let some r ← applyTransitionRules goal then
      return r


  return none


/-- Cache result if it does not have any subgoals. -/
def cacheResult (goal : Goal) (r : Result) : FunPropM Result := do
  modify (fun s => { s with cache := s.cache.insert goal r })
  return r

/-- Cache for failed goals such that `fun_prop` can fail fast next time. -/
def cacheFailure (goal : Goal) : FunPropM Unit := do -- return proof?
  modify (fun s => { s with failureCache := s.failureCache.insert goal })


/-- Main `funProp` function. Returns proof of `e`. -/
partial def main (goal : Goal) : FunPropM (Option Result) := do

  increaseSteps

  -- if function starts with let bindings move them the top of `e` and try again
  if goal.mainFun.isLet then
    return ← funProp (← mapLetTelescope goal.mainFun
      fun _ b => do pure <| (← goal.mkFreshExpr).setArg goal.decl.funArgId b)

  match ← getFunctionData? goal.mainFun (← unfoldNamePred) with
  | .letE f =>
    trace[Debug.Meta.Tactic.fun_prop] "let case on {← ppExpr f}"
    let goal ← goal.updateMainFun f -- update goal with reduced f
    letCase goal goal.mainFun
  | .lam f =>
    trace[Debug.Meta.Tactic.fun_prop] "pi case on {← ppExpr f}"
    let goal ← goal.updateMainFun f -- update goal with reduced f
    applyPiRule goal
  | .data fData =>
    let goal ← goal.updateMainFun (← fData.toExpr) -- update goal with reduced f

    if fData.isIdentityFun then
      applyIdRule goal
    else if fData.isConstantFun then
      applyConstRule goal
    else
      match fData.fn with
      | .fvar id =>
        if id == fData.mainVar.fvarId! then
          bvarAppCase goal fData
        else
          fvarAppCase goal fData
      | .const .. | .proj .. => do
        constAppCase goal fData
      | _ =>
        trace[Debug.Meta.Tactic.fun_prop] "unknown case, ctor: {goal.mainFun.ctorName}\n{← goal.pp}"
        return none

/-- Wrapper around `main` that does caching. -/
def funPropCoreImpl (goal : Goal) : FunPropM (Option Result) := do

  withTraceNode `Meta.Tactic.fun_prop
    (fun _ => do pure m!"{← goal.pp}") do

  -- check cache for successful goals
  if let some r := (← get).cache.get? goal then
    trace[Meta.Tactic.fun_prop] "reusing previously found proof for {← goal.pp}"
    return some r
  else if (← get).failureCache.contains goal then
    trace[Meta.Tactic.fun_prop]
      "skipping proof search, proving {← goal.pp} was tried already and failed"
    return none
  else
    -- run main
    if let some r ← main goal then
      cacheResult goal r
    else
      cacheFailure goal
      return none


-- initialize the forward declaration with the actual implementation
initialize funPropCoreImplRef.set funPropCoreImpl


end Meta.FunProp

end Mathlib
