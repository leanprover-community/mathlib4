/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Batteries.Tactic.Exact

import Mathlib.Tactic.FunProp.Theorems
import Mathlib.Tactic.FunProp.ToBatteries
import Mathlib.Tactic.FunProp.Types
import Mathlib.Lean.Expr.Basic

/-!
## `funProp` core tactic algorithm
-/

namespace Mathlib
open Lean Meta Qq

namespace Meta.FunProp


/-- Synthesize instance of type `type` and
  1. assign it to `x` if `x` is meta variable
  2. check it is equal to `x` -/
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fun_prop]
"{← ppOrigin thmId}, failed to assign instance{indentExpr type}
sythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fun_prop]
      "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false


/-- Synthesize arguments `xs` either with typeclass synthesis, with funProp or with discharger. -/
def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM Bool := do
  let mut postponed : Array Expr := #[]
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      unless (← synthesizeInstance thmId x type) do
        logError s!"Failed to synthesize instance {← ppExpr type} \
        when applying theorem {← ppOrigin' thmId}."
        return false
    else if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue

      -- try function property
      if (← isFunProp type.getForallBody) then
        if let .some ⟨proof⟩ ← funProp type then
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fun_prop]
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
              trace[Meta.Tactic.fun_prop]
                "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
              return false
          else
            logError s!"Failed to prove necessary assumption {← ppExpr type} \
                        when applying theorem {← ppOrigin' thmId}."

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
      when applying theorem {← ppOrigin' thmId}."

      trace[Meta.Tactic.fun_prop]
        "{← ppOrigin thmId}, failed to infer `({← ppExpr x} : {← ppExpr (← inferType x)})`"
      return false

  return true


/-- Try to apply theorem - core function -/
def tryTheoremCore (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr)
    (thmId : Origin) (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fun_prop
    (fun r => return s!"[{ExceptToEmoji.toEmoji r}] applying: {← ppOrigin' thmId}") do

  -- add theorem to the stack
  withTheorem thmId do

  if (← isDefEq type e) then

    if ¬(← synthesizeArgs thmId xs bis funProp) then
      return none
    let proof ← instantiateMVars (mkAppN val xs)

    trace[Meta.Tactic.fun_prop.apply] "{← ppOrigin thmId}, \n{e}"
    return .some { proof := proof }
  else
    trace[Meta.Tactic.fun_prop] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


/-- Try to apply a theorem provided some of the theorem arguments. -/
def tryTheoremWithHint? (e : Expr) (thmOrigin : Origin)
    (hint : Array (Nat×Expr))
    (funProp : Expr → FunPropM (Option Result)) (newMCtxDepth : Bool := false) :
    FunPropM (Option Result) := do
  let go : FunPropM (Option Result) := do
    let thmProof ← thmOrigin.getValue
    let type ← inferType thmProof
    let (xs, bis, type) ← forallMetaTelescope type

    for (i,x) in hint do
      try
        for (id,v) in hint do
          xs[id]!.mvarId!.assignIfDefeq v
      catch _ =>
        trace[Meta.Tactic.fun_trans]
          "failed to use hint {i} `{← ppExpr x} when applying theorem {← ppOrigin thmOrigin}"

    tryTheoremCore xs bis thmProof type e thmOrigin funProp

  if newMCtxDepth then
    withNewMCtxDepth go
  else
    go


/-- Try to apply a theorem -/
def tryTheorem? (e : Expr) (thmOrigin : Origin) (funProp : Expr → FunPropM (Option Result))
    (newMCtxDepth : Bool := false) : FunPropM (Option Result) :=
  tryTheoremWithHint? e thmOrigin #[] funProp newMCtxDepth


/-- Apply lambda calculus rule P fun x => x` -/
def applyIdRule (funPropDecl : FunPropDecl) (e X : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .id)
    | trace[Meta.Tactic.fun_prop]
        "missing identity rule to prove `{← ppExpr e}`"
      return none
  let .id id_X := thm.thmArgs | return none

  tryTheoremWithHint? e (.decl thm.thmName) #[(id_X,X)] funProp

/-- Apply lambda calculus rule P fun x => y` -/
def applyConstRule (funPropDecl : FunPropDecl) (e X y : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .const)
    | trace[Meta.Tactic.fun_prop]
        "missing constant rule to prove `{← ppExpr e}`"
      return none
  let .const id_X id_y := thm.thmArgs | return none

  tryTheoremWithHint? e (.decl thm.thmName) #[(id_X,X),(id_y,y)] funProp

/-- Apply lambda calculus rule P fun f => f i` -/
def applyProjRule (funPropDecl : FunPropDecl) (e x XY : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .forallE n X Y _ := XY | return none

  -- non dependent case
  if ¬(Y.hasLooseBVars) then
    if let .some thm := ext.theorems.find? (funPropDecl.funPropName, .proj) then
      let .proj id_x id_Y := thm.thmArgs | return none
      return ← tryTheoremWithHint? e (.decl thm.thmName) #[(id_x,x),(id_Y,Y)] funProp

  -- dependent case
  -- can also handle non-dependent cases if non-dependent theorem is not available
  let Y := Expr.lam n X Y default

  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .projDep)
    | trace[Meta.Tactic.fun_prop]
        "missing projection rule to prove `{← ppExpr e}`"
      return none
  let .projDep id_x id_Y := thm.thmArgs | return none

  tryTheoremWithHint? e (.decl thm.thmName) #[(id_x,x),(id_Y,Y)] funProp

/-- Apply lambda calculus rule `P f → P g → P fun x => f (g x)` -/
def applyCompRule (funPropDecl : FunPropDecl) (e f g : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .comp)
    | trace[Meta.Tactic.fun_prop]
        "missing composition rule to prove `{← ppExpr e}`"
      return none
  let .comp id_f id_g := thm.thmArgs | return none

  tryTheoremWithHint? e (.decl thm.thmName) #[(id_f,f),(id_g,g)] funProp

/-- Apply lambda calculus rule `∀ y, P (f · y) → P fun x y => f x y` -/
def applyPiRule (funPropDecl : FunPropDecl) (e f : Expr)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let ext := lambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (funPropDecl.funPropName, .pi)
    | trace[Meta.Tactic.fun_prop]
        "missing pi rule to prove `{← ppExpr e}`"
      return none
  let .pi id_f := thm.thmArgs | return none

  tryTheoremWithHint? e (.decl thm.thmName) #[(id_f,f)] funProp


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


/-- Prove function property of using "morphism theorems" e.g. bundled linear map is linear map.  -/
def applyMorRules (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do
  trace[Meta.Tactic.fun_prop.step] "applying morphism theoresm to {← ppExpr e}"

  match ← fData.isMorApplication with
  | .none => throwError "fun_prop bug: ivalid use of mor rules on {← ppExpr e}"
  | .underApplied =>
    applyPiRule funPropDecl e (← fData.toExpr) funProp
  | .overApplied =>
    let .some (f,g) ← fData.peeloffArgDecomposition | return none
    applyCompRule funPropDecl e f g funProp
  | .exact =>

    let ext := morTheoremsExt.getState (← getEnv)
    let candidates ← ext.theorems.getMatchWithScore e false { iota := false, zeta := false }
    let candidates := candidates.map (·.1) |>.flatten

    trace[Meta.Tactic.fun_prop]
      "candidate morphism theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

    for c in candidates do
      if let .some r ← tryTheorem? e (.decl c.thmName) funProp then
        return r

    trace[Meta.Tactic.fun_prop.step] "no theorem matched"
    return none

/-- Prove function property of using "transition theorems" e.g. continuity from linearity.  -/
def applyTransitionRules (e : Expr) (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  let ext := transitionTheoremsExt.getState (← getEnv)
  let candidates ← ext.theorems.getMatchWithScore e false { iota := false, zeta := false }
  let candidates := candidates.map (·.1) |>.flatten

  trace[Meta.Tactic.fun_prop]
    "candidate transition theorems: {← candidates.mapM fun c => ppOrigin (.decl c.thmName)}"

  for c in candidates do
    if ← previouslyUsedThm (.decl c.thmName) then
      trace[Meta.Tactic.fun_prop] "skipping {c.thmName} to prevent potential infinite loop"
    else
      if let .some r ← tryTheorem? e (.decl c.thmName) funProp then
        return r

  trace[Meta.Tactic.fun_prop.step] "no theorem matched"
  return none

/-- Try to remove applied argument. -/
def removeArgRule (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  match fData.args.size with
  | 0 => throwError "fun_prop bug: invalid use of remove arg case {←ppExpr e}"
  | _ =>
    let n := fData.args.size
    let arg := fData.args[n-1]!

    if arg.coe.isSome then
      -- if have to apply morphisms rules if we deal with morphims
      return ← applyMorRules funPropDecl e fData funProp
    else
      let .some (f,g) ← fData.peeloffArgDecomposition | return none
      applyCompRule funPropDecl e f g funProp


/-- Prove function property of `fun f => f x₁ ... xₙ`. -/
def bvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  if (← fData.isMorApplication) != .none then
    applyMorRules funPropDecl e fData funProp
  else
    if let .some (f, g) ← fData.nontrivialDecomposition then
      applyCompRule funPropDecl e f g funProp
    else
      applyProjRule funPropDecl e fData.args[0]!.expr (← fData.domainType) funProp

/-- Get candidate theorems from the environment for function property `funPropDecl` and
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

/-- Get candidate theorems from the local context for function property `funPropDecl` and
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
      let .some (decl,f) ← getFunProp? b | return none
      unless decl.funPropName = funPropDecl.funPropName do return none

      let .data fData ← getFunctionData? f (← unfoldNamePred) {zeta:=false} | return none
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

      return .some thm

    if let .some thm := thm? then
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


/-- Try to apply theorems `thms` to `e` -/
def tryTheorems (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (thms : Array FunctionTheorem) (funProp : Expr → FunPropM (Option Result)) :
    FunPropM (Option Result) := do

  -- none - decomposition not tried
  -- some none - decomposition failed
  -- some some (f, g) - successful decomposition
  let mut dec? : Option (Option (Expr × Expr)) := none

  for thm in thms do

    trace[Meta.Tactic.fun_prop.step] s!"trying theorem {← ppOrigin' thm.thmOrigin}"

    match compare thm.appliedArgs fData.args.size with
    | .lt =>
      trace[Meta.Tactic.fun_prop] s!"removing argument to later use {← ppOrigin' thm.thmOrigin}"
      if let .some r ← removeArgRule funPropDecl e fData funProp then
        return r
      continue
    | .gt =>
      trace[Meta.Tactic.fun_prop] s!"adding argument to later use {← ppOrigin' thm.thmOrigin}"
      if let .some r ← applyPiRule funPropDecl e (← fData.toExpr) funProp then
        return r
      continue
    | .eq =>
      if thm.form == .comp then
        if let .some r ← tryTheorem? e thm.thmOrigin funProp then
          return r
      else

        if thm.mainArgs.size == fData.mainArgs.size then
          if dec?.isNone then
            dec? := .some (← fData.nontrivialDecomposition)
          match dec? with
          | .some .none =>
            if let .some r ← tryTheorem? e thm.thmOrigin funProp then
              return r
          | .some (.some (f,g)) =>
            trace[Meta.Tactic.fun_prop.step]
              s!"decomposing to later use {←ppOrigin' thm.thmOrigin}"
            trace[Meta.Tactic.fun_prop.step]
              s!"decomposition: {← ppExpr f} ∘ {← ppExpr g}"
            if let .some r ← applyCompRule funPropDecl e f g funProp then
              return r
          | _ => continue
        else
          trace[Meta.Tactic.fun_prop.step]
            s!"decomposing in args {thm.mainArgs} to later use {←ppOrigin' thm.thmOrigin}"
          let .some (f,g) ← fData.decompositionOverArgs thm.mainArgs
            | continue
          trace[Meta.Tactic.fun_prop.step]
            s!"decomposition: {← ppExpr f} ∘ {← ppExpr g}"
          if let .some r ← applyCompRule funPropDecl e f g funProp then
            return r
      -- todo: decompose if uncurried and arguments do not match exactly
  return none

/-- Prove function property of `fun x => f x₁ ... xₙ` where `f` is free variable. -/
def fvarAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  -- fvar theorems are almost exclusively in uncurried form so we decompose if we can
  if let .some (f,g) ← fData.nontrivialDecomposition then
    applyCompRule funPropDecl e f g funProp
  else
    let .fvar id := fData.fn | throwError "fun_prop bug: invalid use of fvar app case"
    let thms ← getLocalTheorems funPropDecl (.fvar id) fData.mainArgs fData.args.size
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {←ppExpr (.fvar id)} \
         {← thms.mapM fun thm => ppOrigin' thm.thmOrigin}"

    if let .some r ← tryTheorems funPropDecl e fData thms funProp then
      return r

    if let .some f ← fData.unfoldHeadFVar? then
      let e' := e.setArg funPropDecl.funArgId f
      if let .some r ← funProp e' then
        return r

    if (← fData.isMorApplication) != .none then
      if let .some r ← applyMorRules funPropDecl e fData funProp then
        return r

    if (← fData.nontrivialDecomposition).isNone then
      if let .some r ← applyTransitionRules e funProp then
        return r

    if thms.size = 0 then
      logError s!"No theorems found for `{← ppExpr (.fvar id)}` in order to prove {← ppExpr e}"

    return none


/-- Prove function property of `fun x => f x₁ ... xₙ` where `f` is declared function. -/
def constAppCase (funPropDecl : FunPropDecl) (e : Expr) (fData : FunctionData)
    (funProp : Expr → FunPropM (Option Result)) : FunPropM (Option Result) := do

  let .some (funName,_) := fData.fn.const?
    | throwError "fun_prop bug: invelid use of const app case"
  let globalThms ← getDeclTheorems funPropDecl funName fData.mainArgs fData.args.size

  trace[Meta.Tactic.fun_prop]
    s!"candidate theorems for {funName} {← globalThms.mapM fun thm => ppOrigin' thm.thmOrigin}"

  if let .some r ← tryTheorems funPropDecl e fData globalThms funProp then
    return r

  -- Try local theorems - this is useful for recursive functions
  let localThms ← getLocalTheorems funPropDecl (.decl funName) fData.mainArgs fData.args.size
  if localThms.size ≠ 0 then
    trace[Meta.Tactic.fun_prop]
      s!"candidate local theorems for {funName} \
        {← localThms.mapM fun thm => ppOrigin' thm.thmOrigin}"
  if let .some r ← tryTheorems funPropDecl e fData localThms funProp then
    return r

  if (← fData.isMorApplication) != .none then
    if let .some r ← applyMorRules funPropDecl e fData funProp then
      return r

  if let .some (f,g) ← fData.nontrivialDecomposition then
    if let .some r ← applyCompRule funPropDecl e f g funProp then
      return r
  else
    if let .some r ← applyTransitionRules e funProp then
      return r

  if globalThms.size = 0 &&
     localThms.size = 0 then
     logError s!"No theorems found for `{funName}` in order to prove {← ppExpr e}"

  return none


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

    increaseSteps

    withTraceNode `Meta.Tactic.fun_prop
      (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do

    -- if function starts with let bindings move them the top of `e` and try
    -- again
    if f.isLet then
      return ← letTelescope f fun xs b => do
        let e' := e.setArg funPropDecl.funArgId b
        funProp (← mkLambdaFVars xs e')

    match ← getFunctionData? f (← unfoldNamePred) {zeta:=false} with
    | .letE f =>
      trace[Meta.Tactic.fun_prop.step] "let case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f -- update e with reduced f
      letCase funPropDecl e f funProp
    | .lam f =>
      trace[Meta.Tactic.fun_prop.step] "pi case on {← ppExpr f}"
      let e := e.setArg funPropDecl.funArgId f -- update e with reduced f
      applyPiRule funPropDecl e f funProp
    | .data fData =>
      let e := e.setArg funPropDecl.funArgId (← fData.toExpr) -- update e with reduced f

      if fData.isIdentityFun then
        applyIdRule funPropDecl e (← fData.domainType) funProp
      else if fData.isConstantFun then
        applyConstRule funPropDecl e (← fData.domainType) (Mor.mkAppN fData.fn fData.args) funProp
      else
        match fData.fn with
        | .fvar id =>
          if id == fData.mainVar.fvarId! then
            bvarAppCase funPropDecl e fData funProp
          else
            fvarAppCase funPropDecl e fData funProp
        | .mvar .. => funProp (← instantiateMVars e)
        | .const .. | .proj .. => do
          constAppCase funPropDecl e fData funProp
        | _ =>
          trace[Meta.Tactic.fun_prop.step] "unknown case, ctor: {f.ctorName}\n{e}"
          return none

end
