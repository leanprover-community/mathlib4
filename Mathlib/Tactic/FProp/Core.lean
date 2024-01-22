
/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Qq
import Std.Tactic.Exact
import Mathlib.Tactic.FProp.FPropAttr
import Mathlib.Tactic.FProp.Meta
import Mathlib.Tactic.FProp.ArraySet

namespace Mathlib
open Lean Meta Qq

namespace Meta.FProp

variable {α} (a : α)

private def _root_.Lean.Meta.letTelescopeImpl {α} (e : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := 
  lambdaLetTelescope e λ xs b => do
    if let .some i ← xs.findIdxM? (λ x => do pure ¬(← x.fvarId!.isLetVar)) then
      k xs[0:i] (← mkLambdaFVars xs[i:] b)
    else
      k xs b

private def _root_.Lean.Meta.letTelescope {α n} [MonadControlT MetaM n] [Monad n] (e : Expr) (k : Array Expr → Expr → n α) : n α := 
  map2MetaM (fun k => letTelescopeImpl e k) k

-- TODO: fix the implementation in STD
private def _root_.Lean.Expr.modArgRev (modifier : Expr → Expr) (i : Nat) (e : Expr) : Expr :=
  match i, e with
  |      0, .app f x => .app f (modifier x)
  | (i'+1), .app f x => .app (modArgRev modifier i' f) x
  | _, _ => e

-- TODO: fix the implementation in STD
private def _root_.Lean.Expr.modArg (modifier : Expr → Expr) (i : Nat) (e : Expr) (n := e.getAppNumArgs) : Expr :=
  Expr.modArgRev modifier (n - i - 1) e

-- TODO: fix the implementation in STD
private def _root_.Lean.Expr.setArg (e : Expr) (i : Nat) (x : Expr) (n := e.getAppNumArgs) : Expr :=
  e.modArg (fun _ => x) i n

/--
  Swaps bvars indices `i` and `j`

  NOTE: the indices `i` and `j` do not correspond to the `n` in `bvar n`. Rather
  they behave like indices in `Expr.lowerLooseBVars`, `Expr.liftLooseBVars`, etc.

  TODO: This has to have a better implementation, but I'm still beyond confused with how bvar indices work
-/
def _root_.Lean.Expr.swapBVars (e : Expr) (i j : Nat) : Expr := 

  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray



----------------------------------------------------------------------------------------------------

/-- -/
def unfoldFunHeadRec? (e : Expr) : MetaM (Option Expr) := do
  lambdaLetTelescope e fun xs b => do
    if let .some b' ← reduceRecMatcher? b then
      -- preform some kind of reduction
      let b' := Mor.headBeta b'
      trace[Meta.Tactic.fprop.step] s!"unfolding\n{← ppExpr b}\n==>\n{← ppExpr b'}"
      return .some (← mkLambdaFVars xs b')
    return none

/-- -/
def unfoldFunHead? (e : Expr) : MetaM (Option Expr) := do
  lambdaLetTelescope e fun xs b => do
    if let .some b' ← withTransparency .instances <| unfoldDefinition? b then
      let b' := Mor.headBeta b'
      trace[Meta.Tactic.fprop.step] s!"unfolding\n{← ppExpr b}\n==>\n{← ppExpr b'}"
      return .some (← mkLambdaFVars xs b')
    else if let .some b' ← reduceRecMatcher? b then
      let b' := Mor.headBeta b'
      trace[Meta.Tactic.fprop.step] s!"unfolding\n{← ppExpr b}\n==>\n{← ppExpr b'}"
      return .some (← mkLambdaFVars xs b')

    return none

/-- -/
def synthesizeInstance (thmId : Origin) (x type : Expr) : MetaM Bool := do
  match (← trySynthInstance type) with
  | LOption.some val =>
    if (← withReducibleAndInstances <| isDefEq x val) then
      return true
    else
      trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
      return false
  | _ =>
    trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
    return false


/-- Synthesize arguments `xs` either with typeclass synthesis, with fprop or with discharger.
If succesfull it returns list of subgoals that should be presented to the user.
If fails it returns `none`. -/
def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo) 
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) 
  : FPropM (Option (List MVarId)) := do
  let mut subgoals : List MVarId := []
  for x in xs, bi in bis do
    let type ← inferType x
    if bi.isInstImplicit then
      unless (← synthesizeInstance thmId x type) do
        return .none
    else if (← instantiateMVars x).isMVar then

      -- try type class
      if (← isClass? type).isSome then
        if (← synthesizeInstance thmId x type) then
          continue

      -- try function property
      if (← isFProp type.getForallBody) then
        if let .some ⟨proof, subgoals'⟩ ← fprop (← instantiateMVars type) then
          subgoals := subgoals ++ subgoals'
          if (← isDefEq x proof) then
            continue
          else do
            trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return none

      -- try discharger
      if (← isProp type) then
        if let .some proof ← discharge? type then
          if (← isDefEq x proof) then
            continue 
          else do
            trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
            return none

      trace[Meta.Tactic.fprop.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
      return none

  return .some subgoals


private def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.key)

/-- -/
def tryTheoremCore (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thmId : Origin) 
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  withTraceNode `Meta.Tactic.fprop (fun r => return s!"[{ExceptToEmoji.toEmoji r}] applying: {← ppOrigin' thmId}") do

  if (← isDefEq type e) then

    let .some subgoals ← synthesizeArgs thmId xs bis discharge? fprop | return none
    let proof ← instantiateMVars (mkAppN val xs)

    -- TODO: check that the only mvars in proof are subgoals
    -- if subgoals.length == 0 && (← hasAssignableMVar proof) then 
    --   trace[Meta.Tactic.fprop.apply] "{← ppOrigin thmId}, has unassigned metavariables after unification"
    --   return none

    trace[Meta.Tactic.fprop.apply] "{← ppOrigin thmId}, \n{e}"
    return .some { proof := proof, subgoals := subgoals }
  else
    trace[Meta.Tactic.fprop.unify] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"
    return none


/-- -/
def tryTheorem? (e : Expr) (thm : FPropTheorem)
  (discharge? : Expr → MetaM (Option Expr)) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  withNewMCtxDepth do
    let thmProof ← thm.getProof
    let type ← inferType thmProof
    let (xs, bis, type) ← forallMetaTelescope type
    tryTheoremCore xs bis thmProof type e thm.origin discharge? fprop

/-- -/
def applyIdRule (fpropDecl : FPropDecl) (e X : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .id) 
    | return none
  let .id id_X := thm.thrmArgs | return none
  
  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try 
    xs[id_X]!.mvarId!.assignIfDefeq X
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


-- TODO: try normal theorems if there is no const theorem 
--       this is usefull for proving `IsLinearMap fun x => 0` which is a special case of constant rule
/-- -/
def applyConstRule (fpropDecl : FPropDecl) (e X y : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .const) | return none
  let .const id_X id_y := thm.thrmArgs | return none
  
  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_X]!.mvarId!.assignIfDefeq X
    xs[id_y]!.mvarId!.assignIfDefeq y
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{← ppExpr e}`"
    return none


  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop

/-- -/
def applyProjRule (fpropDecl : FPropDecl) (e x XY : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)

  let .forallE n X Y _ := XY | return none

  -- non dependent case 
  if ¬(Y.hasLooseBVars) then
    if let .some thm := ext.theorems.find? (fpropDecl.fpropName, .proj) then

      let .proj id_x id_Y := thm.thrmArgs | return none

      let proof ← thm.getProof
      let type ← inferType proof
      let (xs, bis, type) ← forallMetaTelescope type

      try
        xs[id_x]!.mvarId!.assignIfDefeq x
        xs[id_Y]!.mvarId!.assignIfDefeq Y
      catch _ =>
        trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{← ppExpr e}`"
        return none

      return ← tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop

  -- dependent case
  -- can also handle non-dependent cases if non-dependent theorem is not available
  let Y := Expr.lam n X Y default

  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .projDep) 
    | trace[Meta.Tactic.fprop.step] "missing proj rule(`P fun f => f x`) for function property `{← ppOrigin (.decl fpropDecl.fpropName)}`"
      return none
  let .projDep id_x id_Y := thm.thrmArgs | return none

  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try 
    xs[id_x]!.mvarId!.assignIfDefeq x
    xs[id_Y]!.mvarId!.assignIfDefeq Y
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop

/-- -/
def applyCompRule (fpropDecl : FPropDecl) (e f g : Expr)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .comp) | return none
  let .comp id_f id_g := thm.thrmArgs | return none
  
  let proof ← thm.getProof
  let type ← inferType proof
  let mut (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_f]!.mvarId!.assignIfDefeq f
    xs[id_g]!.mvarId!.assignIfDefeq g
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{e}`"
    return none


  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop

/-- -/
def applyLetRule (fpropDecl : FPropDecl) (e f g : Expr) 
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .letE) | return none
  let .letE id_f id_g := thm.thrmArgs | return none
  
  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_f]!.mvarId!.assignIfDefeq f
    xs[id_g]!.mvarId!.assignIfDefeq g
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop

/-- -/
def applyPiRule (fpropDecl : FPropDecl) (e f : Expr)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do 

  let ext := fpropLambdaTheoremsExt.getState (← getEnv)
  let .some thm := ext.theorems.find? (fpropDecl.fpropName, .pi) | return none
  let .pi id_f := thm.thrmArgs | return none
  
  let proof ← thm.getProof
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type

  try
    xs[id_f]!.mvarId!.assignIfDefeq f
  catch _ =>
    trace[Meta.Tactic.fprop.discharge] "failed to use `{← ppOrigin (.decl thm.thrmName)}` on `{e}`"
    return none

  tryTheoremCore xs bis proof type e (.decl thm.thrmName) fpropDecl.discharger fprop


/-- Changes the goal from `P fun x => f x₁ x₂ x₃` to `P fun x => f x₁ x₂`
  TODO: be able to provide number of arguments -/
def removeArgRule (fpropDecl : FPropDecl) (e f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do

  lambdaTelescope f fun xs b => do
    if xs.size ≠ 1 then 
      throwError "fprop bug: can't remove arguments from {← ppExpr f}, not a lambda with one argument"

    let xId := xs[0]!.fvarId!

    let .app fn z := b 
      | throwError "fprop bug: can't remove arguments from {← ppExpr f}, body not application"

    if z.containsFVar xId then
      throwError "fprop bug: can't remove argument from function {← ppExpr f}, last arg depends on the lambda argument"

    let f' := .lam `f (← inferType fn) (.app (.bvar 0) z) default
    let g' ← mkLambdaFVars xs fn
    
    applyCompRule fpropDecl e f' g' fprop


-- /-- Is this a valid local fprop hypothesis about free variable? -/
-- def isValidFVarHypothesis? (e : Expr) : MetaM (Option (FPropDecl × FVarFunInfo))


/-- Determina if `e` is talking about a free variable and about which arguments.

For example: 
 - for `Continuous f` this function returns fvar id of `f` and `#[0]`
 - for `Continuous fun x => f x y` this function returns fvar id of `f` and `#[1]`
 - for `Continuous fun (x,y) => f x y` this function returns fvar id of `f` and `#[0,1]`
 - for `Continuous fun xy => f xy.1 xy.2` this function returns fvar id of `f` and `#[0,1]`

This function is assuming:
 - that `e` is taling about function property `fpropDecl`
 - the function `f` in `e` can't be expressed as composition of two non-trivial functions 
   this means that `f == (← splitLambdaToComp f).1` is true -/
def isFVarFProp (fpropDecl : FPropDecl) (e : Expr) : MetaM (Option (FVarId × ArraySet Nat × Nat)) := do

  forallTelescope e fun _ e => do

  let f := e.getArg! fpropDecl.funArgId |>.consumeMData

  if f.isAppOfArity `Function.HasUncurry.uncurry 5 then
    let f := f.appArg!
    let .fvar fvarId := f
      | return none
    let n ← Mor.getArity f
    return .some (fvarId, Array.range n |>.toArraySet, n)

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
        |>.toArraySet
      return (fvarId, ids, args.size)
    | _ => return none
  | f => 
    let n := Mor.getAppNumArgs f
    match Mor.getAppFn f with
    | .fvar fvarId =>  return (fvarId, #[n].toArraySet, n+1)
    | _ => return none


def proveFVarFPropFromLocalTheorems (fpropDecl : FPropDecl) (e : Expr) (fvarId : FVarId) (args : ArraySet Nat) (numAppArgs : Nat)
  (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do

  let lctx ← getLCtx
  for var in lctx do
    let type ← instantiateMVars var.type

    if (var.kind ≠ Lean.LocalDeclKind.auxDecl) then

      let .some (fpropDecl', _) ← getFProp? type.getForallBody 
        | continue
      if fpropDecl'.fpropName ≠ fpropDecl.fpropName then
        continue

      trace[Meta.Tactic.fprop.step] "found potentially applicable local theorem {type}"

      let .some (fvarId', args',numAppArgs') ← isFVarFProp fpropDecl type
        | trace[Meta.Tactic.fprop.step] "not fvar fprop"
          continue
      if fvarId != fvarId' then
        trace[Meta.Tactic.fprop.step] "incorrect fvar"
        continue

      trace[Meta.Tactic.fprop.step] "is applicable"

      -- this local theorem should be directly applicable to e
      if args = args' && numAppArgs = numAppArgs' then

        let thm : FPropTheorem := {
          fpropName := fpropDecl'.fpropName
          keys := []
          levelParams := #[]
          proof := var.toExpr
          origin := .fvar var.fvarId 
        }

        let .some r ← tryTheorem? e thm fpropDecl.discharger fprop
          | continue

        trace[Meta.Tactic.fprop.apply] "local hypothesis {(Expr.fvar var.fvarId)}"
        return .some r

      if args ⊆ args' then

        trace[Meta.Tactic.fprop.step] "found local theorem which talks about more argument than necessary {type}"

        match compare numAppArgs numAppArgs' with
        | .lt => 
          return ← applyPiRule fpropDecl e (e.getArg! fpropDecl.funArgId) fprop
        | .gt => 
          return ← removeArgRule fpropDecl e (e.getArg! fpropDecl.funArgId) fprop
        | .eq => 
          let f := e.getArg! fpropDecl.funArgId

          let .some (f', g') ← splitMorToCompOverArgs f args'
            | continue

          trace[Meta.Tactic.fprop.step] "goal split at `{f'} ∘ {g'}`"

          return ← applyCompRule fpropDecl e f' g' fprop

  trace[Meta.Tactic.fprop.discharge] "no applicable local hypothesis for {e}"
  return none
  

/-- -/
def tryLocalTheorems (fpropDecl : FPropDecl) (e : Expr)
  (fprop : Expr → FPropM (Option Result))
  : FPropM (Option Result) := do 

  let lctx ← getLCtx
  for var in lctx do
    let type ← instantiateMVars var.type
    
    if (var.kind ≠ Lean.LocalDeclKind.auxDecl) then
      let .some (fpropDecl', _) ← getFProp? type.getForallBody 
        | continue
      if fpropDecl'.fpropName ≠ fpropDecl.fpropName then
        continue

      let thm : FPropTheorem := {
        fpropName := fpropDecl'.fpropName
        keys := []
        levelParams := #[]
        proof := var.toExpr
        origin := .fvar var.fvarId 
      }
      
      let .some r ← tryTheorem? e thm fpropDecl.discharger fprop
        | continue

      trace[Meta.Tactic.fprop.apply] "local hypothesis {(Expr.fvar var.fvarId)}"
      return .some r

  trace[Meta.Tactic.fprop.discharge] "no local hypothesis {e}"
  return none

/-- -/
def letCase (fpropDecl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
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
      throwError "dependent type encountered {← ppExpr (Expr.forallE xName xType yType default)} in\n{← ppExpr e}"

    -- let binding can be pulled out of the lambda function
    if ¬(yValue.hasLooseBVar 0) then
      let body := yBody.swapBVars 0 1
      let e' := (.letE yName yType yValue (e.setArg (fpropDecl.funArgId) (.lam xName xType body xBi)) false)
      return ← fprop e'

    match (yBody.hasLooseBVar 0), (yBody.hasLooseBVar 1) with
    | true, true =>
      let f := Expr.lam xName xType (.lam yName yType yBody default) xBi
      let g := Expr.lam xName xType yValue default
      applyLetRule fpropDecl e f g fprop

    | true, false => 
      let f := Expr.lam yName yType yBody default
      let g := Expr.lam xName xType yValue default
      applyCompRule fpropDecl e f g fprop

    | false, _ => 
      let f := Expr.lam xName xType (yBody.lowerLooseBVars 1 1) xBi
      fprop (e.setArg (fpropDecl.funArgId) f)


  | _ => throwError "expected expression of the form `fun x => lam y := ..; ..`"
  -- return none

/-- -/
def bvarAppCase (fpropDecl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do
  let .lam n t (.app g x) bi := f
    | -- this case might not even be possible on the uses of `bvarAppCase`
      trace[Meta.Tactic.fprop.step] "fprop can handle function like {f}"
      return none

  if x.hasLooseBVars then
    -- this case might not even be possible on the uses of `bvarAppCase`
    trace[Meta.Tactic.fprop.step] "fprop can handle function like {f}"
    return none
  
  match g with
  | .bvar 0 => 
    -- return none
    applyProjRule fpropDecl e x t fprop
  | _ => 
    removeArgRule fpropDecl e f fprop
    -- let g := .lam n t g bi
    -- let gType ← inferType g
    -- let .some (_,fType) := gType.arrow?
    --   | trace[Meta.Tactic.fprop.step] "fprop can't handle dependent functions of type {← ppExpr gType} appearing in {← ppExpr f}"
    --     return none

    -- let h := .lam n fType ((Expr.bvar 0).app x) bi
    -- applyCompRule fpropDecl e h g fprop

/-- -/
def fvarAppCase (fpropDecl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do

  let .some (f', g') ← splitMorToComp f
    | throwError "fprop bug: failed to decompose {f}"

  -- trivial case, this prevents an infinite loop
  if (← isDefEq f' f) then      
    trace[Meta.Tactic.fprop.step] "fvar app case: trivial"
    let .some (fvarId, args, n) ← isFVarFProp fpropDecl e
      | trace[Meta.Tactic.fprop.step] "fvar app case: unexpected goal {e}"
        return none
    return ← proveFVarFPropFromLocalTheorems fpropDecl e fvarId args n fprop
  else
    trace[Meta.Tactic.fprop.step] "decomposed into `({f'}) ∘ ({g'})`"
    applyCompRule fpropDecl e f' g' fprop
  
/-- -/
def constAppCase (fpropDecl : FPropDecl) (e : Expr) (f : Expr) (fprop : Expr → FPropM (Option Result)) : FPropM (Option Result) := do

  if let .some f' ← unfoldFunHeadRec? f then
    return ← fprop (e.setArg fpropDecl.funArgId f')

  trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is declared function\n{e}"

  let ext := fpropTheoremsExt.getState (← getEnv)
  let candidates ← ext.theorems.getMatchWithScore e false { iota := false, zeta := false }
  let candidates := candidates.map (·.1) |>.flatten

  let path := (← RefinedDiscrTree.mkDTExpr e { iota := false, zeta := false }).flatten
  trace[Meta.Tactic.fprop.step] "looking up candidates for: {path}"

  trace[Meta.Tactic.fprop.step] "candidate theorems: {← candidates.mapM fun c => ppOrigin c.origin}"

  if candidates.size ≠ 0 then

    for c in candidates do
      if let .some r ← tryTheorem? e c fpropDecl.discharger fprop then
        return r

    trace[Meta.Tactic.fprop.step] "no theorem matched"
    return none
  else
    trace[Meta.Tactic.fprop.step] "no candidates found"
    let .some f' ← unfoldFunHead? f | return none

    let e' := e.setArg fpropDecl.funArgId f'
    return (← fprop e')
    

-- cache if there are no subgoals
/-- -/
def maybeCache (e : Expr) (r : Result) : FPropM (Option Result) := do -- return proof?
  if r.subgoals.length = 0 then
    modify (fun s => { s with cache := s.cache.insert e { expr := q(True), proof? := r.proof} })
  return r

mutual
  /-- -/ 
  partial def fprop (e : Expr) : FPropM (Option Result) := do

    -- check cache
    if let .some { expr := _, proof? := .some proof } := (← get).cache.find? e then
      trace[Meta.Tactic.fprop.cache] "cached result for {e}"
      return .some { proof := proof, subgoals := [] }

    else
      -- take care of forall and let binders and run main
      match e with
      | .letE .. => 
        letTelescope e fun xs b => do
          let .some r ← fprop b
            | return none
          maybeCache e {proof := ← mkLambdaFVars xs r.proof, subgoals := r.subgoals}
      | .forallE .. => 
        forallTelescope e fun xs b => do
          let .some r ← fprop b
            | return none
          maybeCache e {proof := ← mkLambdaFVars xs r.proof, subgoals := r.subgoals}
      | .mdata _ e' => fprop e'
      | .mvar _ => instantiateMVars e >>= fprop
      | _ => 
        let .some r ← main e
          | return none
        maybeCache e r
        
  /-- -/
  partial def main (e : Expr) : FPropM (Option Result) := do

    let .some (fpropDecl, f) ← getFProp? e
      | return none

    let f := f.consumeMData.eta
    -- eta expand if `f` is not lambda function
    let f ← 
      if f.isLambda 
      then pure f
      else do
        let X := (← inferType f).bindingDomain!
        pure (.lam `x X (f.app (.bvar 0)) default)
    
    let e := e.setArg fpropDecl.funArgId f

    withTraceNode `Meta.Tactic.fprop (fun r => do pure s!"[{ExceptToEmoji.toEmoji r}] {← ppExpr e}") do

    match f with
    | .letE .. => letTelescope f fun xs b => do 
      trace[Meta.Tactic.fprop.step] "Case `P (let x := ..; f)`\n{e}"
      let e' := e.setArg fpropDecl.funArgId b
      fprop (← mkLambdaFVars xs e')

    | .lam xName xType xBody xBi => 

      match xBody.consumeMData.headBeta.consumeMData with
      | (.bvar 0) => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => x)\n{e}"
        applyIdRule fpropDecl e xType fprop

      | .letE .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x => let y := ..; ..)\n{e}"
        letCase fpropDecl e f fprop

      | .lam  .. => 
        trace[Meta.Tactic.fprop.step] "case `P (fun x y => f x y)`\n{e}"
        applyPiRule fpropDecl e f fprop

      | .mvar .. => fprop (← instantiateMVars e)

      | xBody => do
        if !(xBody.hasLooseBVar 0) then
          trace[Meta.Tactic.fprop.step] "case `P (fun x => y)`\n{e}"
          applyConstRule fpropDecl e xType xBody fprop
        else 
          let f' := Expr.lam xName xType xBody xBi
          let g := Mor.getAppFn xBody
          let nargs := Mor.getAppNumArgs xBody

          match g with 
          | .fvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun x => f x)` where `f` is free variable\n{e}"
            fvarAppCase fpropDecl e f' fprop
          | .bvar .. => 
            trace[Meta.Tactic.fprop.step] "case `P (fun f => f x)`\n{e}"
            bvarAppCase fpropDecl e f' fprop
          | .mvar .. => 
            fprop (← instantiateMVars e)
          | .const n _ => do
            let arity ← Mor.constArity n
            match compare arity nargs with
            | .eq => constAppCase fpropDecl e f fprop
            | .gt => applyPiRule fpropDecl e f fprop
            | .lt => removeArgRule fpropDecl e f fprop
          | .proj .. | .app .. => do
            constAppCase fpropDecl e f fprop
          | _ => 
            trace[Meta.Tactic.fprop.step] "unknown case, ctor: {f.ctorName}\n{e}"
            return none

    | _ => throwError "fprop bug: non-lambda case"
    -- | .mvar _ => do
    --   fprop (← instantiateMVars e)
    -- | f => 
    --   let fn := Mor.getAppFn f
    --   let nargs := Mor.getAppNumArgs f
    --   match fn with 
    --   | .fvar .. => do
    --     fvarAppCase fpropDecl e f fprop
    --   | .const n _ => do
    --     match compare (← constArity n) (nargs+1) with
    --     | .eq => constAppCase fpropDecl e f fprop
    --     | .gt => applyPiRule fpropDecl e f fprop
    --     | .lt => removeArgRule fpropDecl e f fprop
    --   | .proj .. => do
    --     constAppCase fpropDecl e f fprop
    --   | _ => 
    --     trace[Meta.Tactic.fprop.step] "unknown case, ctor: {f.ctorName}\n{e}"
    --     return none

end
