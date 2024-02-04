/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Qq
import Std.Tactic.Exact

import Mathlib.Tactic.FunProp.ToStd
import Mathlib.Tactic.FunProp.Theorems

/-!
## `funProp` core tactic algorithm
-/

namespace Mathlib
open Lean Meta Qq

namespace Meta.FunProp

/-- unfold function head -/
def FunctionData.unfold? (fData : FunctionData) : FunPropM (Option Expr) := do
  withLCtx fData.lctx fData.insts do
    let .some name ← fData.getFnConstName?
      | return none

    let cfg ← readThe Config

    let mut didUnfold := false
    let mut body := Mor.mkAppN fData.fn fData.args

    if cfg.constToUnfold.contains name || (← isReducible name) then
      if let .some body' ← withTransparency .default <| unfoldDefinition? body then
        trace[Meta.Tactic.fun_prop.unfold] "unfolding {body} ==> {body'}"
        didUnfold := true
        body := body'
        -- try unfold again if we have projection
        if body'.getAppFn.isProj then
          if let .some fn' ← reduceProj? body'.getAppFn then
            trace[Meta.Tactic.fun_prop.unfold] "unfolding {body'.getAppFn} ==> {fn'}"
            body := fn'.beta body'.getAppArgs

    if didUnfold then
      return ← mkLambdaFVars #[fData.mainVar] body.headBeta
    else
      return none

/-- Unfold function body head recursors and matches -/
def unfoldFunHeadRec? (e : Expr) : MetaM (Option Expr) := do
  lambdaLetTelescope e fun xs b => do
    if let .some b' ← reduceRecMatcher? b then
      -- preform some kind of reduction
      let b' := Mor.headBeta b'
      trace[Meta.Tactic.fun_prop.step] s!"unfolding\n{← ppExpr b}\n==>\n{← ppExpr b'}"
      return .some (← mkLambdaFVars xs b')
    return none

/-- Synthesize instance of type `type` and
  1. assign it to `x` if `x` is meta veriable
  2. check it is equal to `x` -/
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop.discharge]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
sythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false


/-- Synthesize arguments `xs` either with typeclass synthesis, with funProp or with discharger. -/
def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo)
    (discharge? : Expr → MetaM (Option Expr)) (funProp : Expr → FunPropM (Option Result)) :
    FunPropM Bool := do
  let mut postponed : Array Expr := #[]
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      unless (← synthesizeInstance thmId x type) do
        return false
    else if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue

      -- try function property
      if (← isFunProp type.getForallBody) then
        if let .some ⟨proof⟩ ← withReader (·.addThm thmId) (funProp type) then
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fun_prop.discharge]
              "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return false
      else
        -- try user provided discharger
        let cfg : Config ← read
        if (← isProp type) then
          if let .some proof ← cfg.disch type then
            if (← isDefEq x proof) then
              continue
            else do
              trace[Meta.Tactic.fun_prop.discharge]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false

        -- try function property specific discharger
        if (← isProp type) then
          if let .some proof ← discharge? type then
            if (← isDefEq x proof) then
              continue
            else do
              trace[Meta.Tactic.fun_prop.discharge]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false

      if ¬(← isProp type) then
        postponed := postponed.push x
        continue
      else

        trace[Meta.Tactic.fun_prop.discharge]
          "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
        return false

  for x in postponed do
    if (← instantiateMVars x).isMVar then
      trace[Meta.Tactic.fun_prop.discharge]
        "{← ppOrigin thmId}, failed to infer data {indentExpr x}"
      return false

  return true


private def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.key)

/-- Try to apply theorem - core function -/
def tryTheoremCore (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr)
    (thmId : Origin) (discharge? : Expr → MetaM (Option Expr))
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fun_prop
    (fun r => return s!"[{ExceptToEmoji.toEmoji r}] applying: {← ppOrigin' thmId}") do

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs bis discharge? funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    trace[Meta.Tactic.fun_prop.apply] "{← ppOrigin thmId}, \n{e}"
    return .some { proof := proof }
  else
    trace[Meta.Tactic.fun_prop.unify] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


/-- Try to apply declared theorem -/
def tryTheorem? (e : Expr) (thmName : Name) (discharge? : Expr → MetaM (Option Expr))
    (funProp : Expr → FunPropM (Option Result)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof ← mkConstWithFreshMVarLevels thmName
    let type ← inferType thmProof
    let (xs, bis, type) ← forallMetaTelescope type
    tryTheoremCore xs bis thmProof type e (.decl thmName) discharge? funProp

  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go

/-- Try to apply local theorem -/
def tryLocalTheorem? (e : Expr) (fvarId : FVarId) (discharge? : Expr → MetaM (Option Expr))
    (funProp : Expr → FunPropM (Option Result)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof := .fvar fvarId
    let type ← inferType thmProof
    let (xs, bis, type) ← forallMetaTelescope type
    tryTheoremCore xs bis thmProof type e (.fvar fvarId) discharge? funProp

  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go

/-- Apply lambda calculus rule P fun x => x` -/
def applyIdRule (funPropDecl : FunPropDecl) (e X : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .id)
    | trace[Meta.Tactic.fun_prop]
        "missing identity rule to prove `{← ppExpr e}`"
      return none
  let .id id_X := thm.thmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_X]!.mvarId!.assignIfDefeq X
  catch _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp

/-- Apply lambda calculus rule P fun x => y` -/
def applyConstRule (funPropDecl : FunPropDecl) (e X y : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .const)
    | trace[Meta.Tactic.fun_prop]
        "missing constant rule to prove `{← ppExpr e}`"
      return none
  let .const id_X id_y := thm.thmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_X]!.mvarId!.assignIfDefeq X
    xs[id_y]!.mvarId!.assignIfDefeq y
  catch _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{← ppExpr e}`"
    return none


  tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp

/-- Apply lambda calculus rule P fun f => f i` -/
def applyProjRule (funPropDecl : FunPropDecl) (e x XY : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)

  let .forallE n X Y _ := XY | return none

  -- non dependent case
  if ¬(Y.hasLooseBVars) then
    if let .some thm := ext.theorems.find? (funPropDecl.funPropName, .proj) then

      let .proj id_x id_Y := thm.thmArgs | return none

      let proof ← thm.getProof
      let type ← inferType proof
      let (xs, bis, type) ← forallMetaTelescope type

      try
        xs[id_x]!.mvarId!.assignIfDefeq x
        xs[id_Y]!.mvarId!.assignIfDefeq Y
      catch _ =>
        trace[Meta.Tactic.fun_prop.discharge]
          "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{← ppExpr e}`"
        return none

      return ← tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp

  -- dependent case
  -- can also handle non-dependent cases if non-dependent theorem is not available
  let Y := Expr.lam n X Y default

  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .projDep)
    | trace[Meta.Tactic.fun_prop]
        "missing projection rule to prove `{← ppExpr e}`"
      return none
  let .projDep id_x id_Y := thm.thmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_x]!.mvarId!.assignIfDefeq x
    xs[id_Y]!.mvarId!.assignIfDefeq Y
  catch _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp

/-- Apply lambda calculus rule `P f → P g → P fun x => f (g x)` -/
def applyCompRule (funPropDecl : FunPropDecl) (e f g : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .comp)
    | trace[Meta.Tactic.fun_prop]
        "missing composition rule to prove `{← ppExpr e}`"
      return none
  let .comp id_f id_g := thm.thmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let mut (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_f]!.mvarId!.assignIfDefeq f
    xs[id_g]!.mvarId!.assignIfDefeq g
  catch _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{e}`"
    return none


  tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp

/-- Apply lambda calculus rule `∀ y, P (f · y) → P fun x y => f x y` -/
def applyPiRule (funPropDecl : FunPropDecl) (e f : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .pi)
    | trace[Meta.Tactic.fun_prop]
        "missing pi rule to prove `{← ppExpr e}`"
      return none
  let .pi id_f := thm.thmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_f]!.mvarId!.assignIfDefeq f
  catch _ =>
    trace[Meta.Tactic.fun_prop.discharge]
      "failed to use `{← ppOrigin (.decl thm.thmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thmName) funPropDecl.discharger funProp


/-- Changes the goal from `P fun x => f x₁ x₂ x₃` to `P fun x => f x₁ x₂`
  TODO: be able to provide number of arguments -/
def removeArgRule (funPropDecl : FunPropDecl) (e f : Expr)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  lambdaTelescope f fun xs b => do
    if xs.size ≠ 1 then
      throwError
        "funProp bug: can't remove arguments from {← ppExpr f}, not a lambda with one argument"

    let xId := xs[0]!.fvarId!

    let .app fn z := b
      | throwError "funProp bug: can't remove arguments from {← ppExpr f}, body not application"

    if z.containsFVar xId then
      return none

    let f' := .lam `f (← inferType fn) (.app (.bvar 0) z) default
    let g' ← mkLambdaFVars xs fn

    applyCompRule funPropDecl e f' g' funProp


-- /-- Is this a valid local funProp hypothesis about free variable? -/
-- def isValidFVarHypothesis? (e : Expr) : MetaM (Option (FunPropDecl × FVarFunInfo))


/-- Determina if `e` is talking about a free variable and about which arguments.

For example:
 - for `Continuous f` this function returns fvar id of `f` and `#[0]`
 - for `Continuous fun x => f x y` this function returns fvar id of `f` and `#[1]`
 - for `Continuous fun (x,y) => f x y` this function returns fvar id of `f` and `#[0,1]`
 - for `Continuous fun xy => f xy.1 xy.2` this function returns fvar id of `f` and `#[0,1]`

This function is assuming:
 - that `e` is taling about function property `funPropDecl`
 - the function `f` in `e` can't be expressed as composition of two non-trivial functions
   this means that `f == (← splitLambdaToComp f).1` is true -/
def isFVarFunProp (funPropDecl : FunPropDecl) (e : Expr) :
    MetaM (Option (FVarId × Array Nat × Nat)) := do

  forallTelescope e fun _ e => do

  let f := e.getArg! funPropDecl.funArgId |>.consumeMData

  if f.isAppOfArity `Function.HasUncurry.uncurry 5 then
    let f := f.appArg!
    let .fvar fvarId := f
      | return none
    let n ← Mor.getArity f
    return .some (fvarId, Array.range n, n)

  let f := (← unfoldFunHeadRec? f).getD f

  match (← whnf f) with
  | .lam _ _ b _ =>
    match Mor.getAppFn b with
    | .fvar fvarId =>
      let args := Mor.getAppArgs b
      -- we do not check the exact form of arguments as we assume `f == (← splitLambdaToComp f).1`
      -- thus checking for loose bvar should be enough
      let ids := args
        |>.mapIdx (fun i arg => if arg.expr.hasLooseBVars then some i.1 else none)
        |>.filterMap id
      return (fvarId, ids, args.size)
    | _ => return none
  | f =>
    let n := Mor.getAppNumArgs f
    match Mor.getAppFn f with
    | .fvar fvarId =>  return (fvarId, #[n], n+1)
    | _ => return none


/-- Prove function property of free variable by using local hypothesis. -/
def proveFVarFunPropFromLocalTheorems (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  let .fvar fvarId := fData.fn | return none
  let args := fData.mainArgs
  let numAppArgs := fData.args.size

  let lctx ← getLCtx
  for var in lctx do
    let type ← instantiateMVars var.type

    if (var.kind ≠ Lean.LocalDeclKind.auxDecl) then

      let .some (funPropDecl', _) ← getFunProp? type.getForallBody
        | continue
      if funPropDecl'.funPropName ≠ funPropDecl.funPropName then
        continue

      trace[Meta.Tactic.fun_prop.step] "found potentially applicable local theorem {type}"

      let .some (fvarId', args',numAppArgs') ← isFVarFunProp funPropDecl type
        | trace[Meta.Tactic.fun_prop.step] "not fvar funProp"
          continue
      if fvarId != fvarId' then
        trace[Meta.Tactic.fun_prop.step] "incorrect fvar"
        continue

      trace[Meta.Tactic.fun_prop.step] "is applicable"

      -- this local theorem should be directly applicable to e
      if args = args' && numAppArgs = numAppArgs' then

        let .some r ← tryLocalTheorem? e var.fvarId funPropDecl.discharger funProp
          | continue

        trace[Meta.Tactic.fun_prop.apply] "local hypothesis {(Expr.fvar var.fvarId)}"
        return .some r

      if isOrderedSubsetOf args args' then

        match compare numAppArgs numAppArgs' with
        | .lt =>
          return ← applyPiRule funPropDecl e (e.getArg! funPropDecl.funArgId) funProp
        | .gt =>
          return ← removeArgRule funPropDecl e (e.getArg! funPropDecl.funArgId) funProp
        | .eq =>
          let f := e.getArg! funPropDecl.funArgId

          let .some (f', g') ← splitMorToCompOverArgs f args'
            | continue

          trace[Meta.Tactic.fun_prop.step] "goal split at `{f'} ∘ {g'}`"

          return ← applyCompRule funPropDecl e f' g' funProp

  trace[Meta.Tactic.fun_prop.discharge] "no applicable local hypothesis for {e}"
  return none


/-- Prove function property of using local hypothesis. -/
def tryLocalTheorems (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let lctx ← getLCtx
  for var in lctx do
    let type ← instantiateMVars var.type

    if (var.kind ≠ Lean.LocalDeclKind.auxDecl) then
      let .some (funPropDecl', _) ← getFunProp? type.getForallBody
        | continue
      if funPropDecl'.funPropName ≠ funPropDecl.funPropName then
        continue

      let .some r ← tryLocalTheorem? e var.fvarId funPropDecl.discharger funProp
        | continue

      trace[Meta.Tactic.fun_prop.apply] "local hypothesis {(Expr.fvar var.fvarId)}"
      return .some r

  trace[Meta.Tactic.fun_prop.discharge] "no local hypothesis {e}"
  return none

/-- Prove function property of `fun x => let y := g x; f x y`. -/
def letCase (funPropDecl : FunPropDecl) (e : Expr) (f : Expr)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do
  match f with
  | .lam xName xType (.letE yName yType yValue yBody _) xBi => do
    let yType  := yType.consumeMData
    let yValue := yValue.consumeMData
    let yBody  := yBody.consumeMData
    -- We perform reduction because the type is quite often of the form
    -- `(fun x => Y) #0` which is just `Y`
    -- Usually this is caused by the usage of `FunLike`
    let yType := yType.headBeta
    if (yType.hasLooseBVar 0) then
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)}"

    -- let binding can be pulled out of the lambda function
    if ¬(yValue.hasLooseBVar 0) then
      let body := yBody.swapBVars 0 1
      let e' := .letE yName yType yValue (nonDep := false)
        (e.setArg (funPropDecl.funArgId) (.lam xName xType body xBi))
      return ← funProp e'

    match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
    | true, true =>
      let f ← mkUncurryFun 2 (Expr.lam xName xType (.lam yName yType yBody default) xBi)
      let g := Expr.lam xName xType (binderInfo := default)
        (mkAppN (← mkConstWithFreshMVarLevels ``Prod.mk) #[xType,yType,.bvar 0, yValue])
      applyCompRule funPropDecl e f g funProp

    | true, false =>
      let f := Expr.lam yName yType yBody default
      let g := Expr.lam xName xType yValue default
      applyCompRule funPropDecl e f g funProp

    | false, _ =>
      let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
      funProp (e.setArg (funPropDecl.funArgId) f)


  | _ => throwError "expected expression of the form `fun x => lam y := ..; ..`"
  -- return none


/-- Prove function property of `fun f => f x₁ ... xₙ`. -/
def bvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (f : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  match f.args.size with
  | 0 => throwError "funProp bug: invalid use of `bvarAppCase`"
  | 1 =>
    if f.args[0]!.coe.isNone then
      applyProjRule funPropDecl e f.args[0]!.expr (← f.domainType) funProp
    else
      throwError "funProp unhandled case: {← ppExpr e}"
  | _ => removeArgRule funPropDecl e (← f.toExpr) funProp


/-- Prove function property of using "morphism theorems" e.g. bundled linear map is linear map.  -/
def applyMorRules (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let .some nargs := fData.getCoeAppNumArgs?
    | return none

  match compare nargs 6 with
  | .lt => applyPiRule funPropDecl e (← fData.toExpr) funProp
  | .gt => removeArgRule funPropDecl e (← fData.toExpr) funProp
  | .eq =>
    let ext := morTheoremsExt.getState (← getEnv)
    let candidates ← ext.theorems.getMatchWithScore e false { iota := false, zeta := false }
    let candidates := candidates.map (·.1) |>.flatten

    trace[Meta.Tactic.fun_prop]
      "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

    for c in candidates do
      if let .some r ← tryTheorem? e c.thmName funPropDecl.discharger funProp then
        return r

    trace[Meta.Tactic.fun_prop.step] "no theorem matched"
    return none

/-- Prove function property of using "transition theorems" e.g. continuity from linearity.  -/
def applyTransitionRules (funPropDecl : FunPropDecl) (e : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := transitionTheoremsExt.getState (← getEnv)
  let candidates ← ext.theorems.getMatchWithScore e false { iota := false, zeta := false }
  let candidates := candidates.map (·.1) |>.flatten

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  let d := (← get).transitionDepth
  let md := (← read).maxTransitionDepth
  if d ≥ md then
    trace[Meta.Tactic.fun_prop] "maximum transition depth({d}) reached"
    return none

  for c in candidates do
    if (← getLastUsedTheoremName) == .some c.thmName then
      trace[Meta.Tactic.fun_prop]
        "skipping {← ppOrigin (.decl c.thmName)}, can't use it twice in a row"
      continue
    if let .some r ← fun cfg state =>
      let state := {state with transitionDepth := d+1}
      tryTheorem? e c.thmName funPropDecl.discharger funProp (newMCtxDepth := false) cfg state
      then return r

  trace[Meta.Tactic.fun_prop.step] "no theorem matched"
  return none



/-- Prove function property of `fun x => f x₁ ... xₙ` where `f` is declared function. -/
def constAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let f ← fData.toExpr

  -- todo: do unfolding when constructing FunctionData
  if let .some f' ← unfoldFunHeadRec? f then
    return ← funProp (e.setArg funPropDecl.funArgId f')

  let .some functionName ← fData.getFnConstName?
    | return none

  let thms ← getTheoremsForFunction functionName funPropDecl.funPropName
  let thms := thms.filter (fun thm => isOrderedSubsetOf fData.mainArgs thm.mainArgs)
  trace[Meta.Tactic.fun_prop]
    "applicable theorems for {functionName}: {thms.map fun thm => toString thm.thmName}"

  -- todo: sort theorems based on relevance

  for thm in thms.reverse do
    match compare thm.appliedArgs fData.args.size with
    | .lt =>
      if let .some prf ← removeArgRule funPropDecl e f funProp then
        return prf
    | .gt =>
      if let .some prf ← applyPiRule funPropDecl e f funProp then
        return prf
    | .eq =>
      match thm.form with
      | .uncurried =>
        if let .some (f',g') ← fData.nontrivialDecomposition then
          if let .some r ← applyCompRule funPropDecl e f' g' funProp then
            return r
        else
          if let .some r ← tryTheorem? e thm.thmName funPropDecl.discharger funProp then
            return r
      | .comp =>
        if let .some r ← tryTheorem? e thm.thmName funPropDecl.discharger funProp then
          return r

  -- try morphism theorems
  if let .some r ← applyMorRules funPropDecl e fData funProp then
    return r

  -- todo: do unfolding when constructing FunctionData
  if let .some f' ← fData.unfold? then
    let e := e.setArg funPropDecl.funArgId f'
    if let .some r ← funProp e then
      return r

  -- if no theorems found try transition theorems
  -- TODO: maybe count the number of theorems that actually unify
  --       I'm worried that adding a theorem might prevent this branch from happening and break
  --       previously working proof
  if thms.size = 0 then
    -- apply transition theorems only on functions that can't be decomposed
    if let .some (f', g') ← fData.nontrivialDecomposition then
      applyCompRule funPropDecl e f' g' funProp
    else
      return ← applyTransitionRules funPropDecl e funProp
  else
    return none

/-- Prove function property of `fun x => f x₁ ... xₙ` where `f` is free variable. -/
def fvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  -- try morphism theorems
  if let .some r ← applyMorRules funPropDecl e fData funProp then
    return r

  if let .some (f,g) ← fData.nontrivialDecomposition then
    applyCompRule funPropDecl e f g funProp
  else
    if let .some prf ← proveFVarFunPropFromLocalTheorems funPropDecl e fData funProp then
      return prf
    else
      -- try transition rules as last resort
      return ← applyTransitionRules funPropDecl e funProp


/-- Cache result if it does not have any subgoals. -/
def cacheResult (e : Expr) (r : Result) : FunPropM Result := do -- return proof?
  modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

mutual
  /-- Main `funProp` function. Returns proof of `e`. -/
  partial def funProp (e : Expr) : FunPropM (Option Result) := do

    -- check cache
    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fun_prop.cache] "cached result for {e}"
      return .some { proof := proof }
    else
      -- take care of forall and let binders and run main
      match e with
      | .letE .. =>
        letTelescope e fun xs b => do
          let .some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof }
      | .forallE .. =>
        forallTelescope e fun xs b => do
          let .some r ← funProp b
            | return none
          cacheResult e {proof := ← mkLambdaFVars xs r.proof }
      | .mdata _ e' => funProp e'
      | .mvar _ => instantiateMVars e >>= funProp
      | _ =>
        let .some r ← main e
          | return none
        cacheResult e r

  /-- Main `funProp` function. Returns proof of `e`. -/
  private partial def main (e : Expr) : FunPropM (Option Result) := do

    let .some (funPropDecl, f) ← getFunProp? e
      | return none

    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do

    -- if function starts with let bindings move them the top of `e` and try
    -- again
    if f.isLet then
      return ← letTelescope f fun xs b => do
        trace[Meta.Tactic.fun_prop.step] "Case `P (let x := ..; f)`\n{e}"
        let e' := e.setArg funPropDecl.funArgId b
        funProp (← mkLambdaFVars xs e')

    -- make sure `f` is lambda with at least one bound variable
    let f ← etaExpand1 f
    -- reset `f` to the new form in `e`
    -- todo: remove this as it should not be necessary but some parts of the
    --       code still relies on this
    let e := e.setArg funPropDecl.funArgId f

    let .lam _xName xType xBody _xBi := f
      | throwError "funProp bug: function {← ppExpr f} is in invalid form"

    match xBody.consumeMData.headBeta.consumeMData with
    | (.bvar 0) =>
      trace[Meta.Tactic.fun_prop.step] "case `P (fun x => x)\n{e}"
      applyIdRule funPropDecl e xType funProp

    | .letE .. =>
      trace[Meta.Tactic.fun_prop.step] "case `P (fun x => let y := ..; ..)\n{e}"
      letCase funPropDecl e f funProp

    | .lam  .. =>
      trace[Meta.Tactic.fun_prop.step] "case `P (fun x y => f x y)`\n{e}"
      applyPiRule funPropDecl e f funProp

    | .mvar .. => funProp (← instantiateMVars e)

    | xBody => do

      if ¬xBody.hasLooseBVars then
        trace[Meta.Tactic.fun_prop.step] "case `P (fun x => y)`\n{e}"
        applyConstRule funPropDecl e xType xBody funProp
      else
        let fData ← getFunctionData f

        match fData.fn with
        | .fvar id =>
          if id == fData.mainVar.fvarId! then
            trace[Meta.Tactic.fun_prop.step] "case `P (fun f => f x)`\n{e}"
            bvarAppCase funPropDecl e fData funProp
          else
            trace[Meta.Tactic.fun_prop.step]
              "case `P (fun x => f x)` where `f` is free variable\n{e}"
            fvarAppCase funPropDecl e fData funProp
        | .mvar .. =>
          funProp (← instantiateMVars e)
        | .const .. | .proj .. => do
          constAppCase funPropDecl e fData funProp
        | _ =>
          trace[Meta.Tactic.fun_prop.step] "unknown case, ctor: {f.ctorName}\n{e}"
          return none

end
