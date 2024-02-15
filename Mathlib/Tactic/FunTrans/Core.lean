/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Qq
import Std.Tactic.Exact

import Mathlib.Tactic.FunTrans.Theorems
import Mathlib.Tactic.FunTrans.Types
import Mathlib.Tactic.FunProp.Core

/-!
## `funTrans` core tactic algorithm
-/

namespace Mathlib
open Lean Meta Qq

namespace Meta.FunTrans

def runFunProp (e : Expr) : SimpM (Option Expr) := do
  let cache := (← get).cache
  modify (fun s => { s with cache := {}}) -- hopefully this prevent duplicating the cache
  let config : FunProp.Config := (← funTransConfig.get).funPropConfig
  let state  : FunProp.State := { cache := cache }
  let (result?, state) ← FunProp.funProp e |>.run config state
  modify (fun simpState => { simpState with cache := state.cache })

  match result? with
  | .some r => return r.proof
  | .none => return .none


def synthesizeArgs (thmId : Origin) (xs : Array Expr) (bis : Array BinderInfo) : SimpM Bool := do
  for x in xs, bi in bis do
    let type ← inferType x
    -- Note that the binderInfo may be misleading here:
    -- `simp [foo _]` uses `abstractMVars` to turn the elaborated term with
    -- mvars into the lambda expression `fun α x inst => foo x`, and all
    -- its bound variables have default binderInfo!
    if bi.isInstImplicit then
      unless (← synthesizeInstance x type) do
        return false
    else if (← instantiateMVars x).isMVar then
      -- A hypothesis can be both a type class instance as well as a proposition,
      -- in that case we try both TC synthesis and the discharger
      -- (because we don't know whether the argument was originally explicit or instance-implicit).
      if (← isClass? type).isSome then
        if (← synthesizeInstance x type) then
          continue

      trace[Meta.Tactic.fun_trans] "synthesizing arg {type}"

      if (← isProp type) then

        trace[Meta.Tactic.fun_trans] "running fun_prop on {type}"
        if let .some r ← runFunProp type then
          x.mvarId!.assign r
          trace[Meta.Tactic.fun_trans] "success"
          continue
        else
          trace[Meta.Tactic.fun_trans] "failed"


      trace[Meta.Tactic.fun_trans.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
      return false
      -- if (← isProp type) then
      --   return false
        -- trace[Meta.Tactic.fun_trans.discharge] "{← ppOrigin thmId}, failed to assign proof{indentExpr type}"
        -- -- We save the state, so that `UsedTheorems` does not accumulate
        -- -- `simp` lemmas used during unsuccessful discharging.
        -- let usedTheorems := (← get).usedTheorems
        -- match (← discharge? type) with
        -- | some proof =>
        --   unless (← isDefEq x proof) do

        --     modify fun s => { s with usedTheorems }
        --     return false
        -- | none =>
        --   trace[Meta.Tactic.fun_trans.discharge] "{← ppOrigin thmId}, failed to discharge hypotheses{indentExpr type}"
        --   modify fun s => { s with usedTheorems }

  return true
where
  synthesizeInstance (x type : Expr) : SimpM Bool := do
    match (← trySynthInstance type) with
    | LOption.some val =>
      if (← withReducibleAndInstances <| isDefEq x val) then
        return true
      else
        trace[Meta.Tactic.fun_trans.discharge] "{← ppOrigin thmId}, failed to assign instance{indentExpr type}\nsythesized value{indentExpr val}\nis not definitionally equal to{indentExpr x}"
        return false
    | _ =>
      trace[Meta.Tactic.fun_trans.discharge] "{← ppOrigin thmId}, failed to synthesize instance{indentExpr type}"
      return false


private def ppOrigin' (origin : Origin) : MetaM String := do
  match origin with
  | .fvar id => return s!"{← ppExpr (.fvar id)} : {← ppExpr (← inferType (.fvar id))}"
  | _ => pure (toString origin.key)


def tryTheoremCore (lhs : Expr) (xs : Array Expr) (bis : Array BinderInfo) (val : Expr) (type : Expr) (e : Expr) (thmId : Origin) : SimpM (Option Simp.Result) := do
  withTraceNode `Meta.Tactic.fun_trans
    (fun r => return s!"[{ExceptToEmoji.toEmoji r}] applying: {← ppOrigin' thmId}") do

  unless (← isDefEq lhs e) do
    trace[Meta.Tactic.fun_trans.unify] "failed to unify {← ppOrigin thmId}\n{type}\nwith\n{e}"

  if ¬(← synthesizeArgs thmId xs bis) then
    return none

  let proof ← instantiateMVars (mkAppN val xs)
  let rhs := (← instantiateMVars type).appArg!
  if e == rhs then
    return none
  trace[Meta.Tactic.fun_trans.rewrite] "{← ppOrigin thmId}, \n{e}\n==>\n{rhs}"
  return .some { expr := rhs, proof? := proof }


def tryTheoremWithHint (e : Expr) (thmName : Name) (hint : Array (Nat × Expr)) : SimpM (Option Simp.Result) := do

  let proof ← mkConstWithFreshMVarLevels thmName
  let type ← inferType proof
  let (xs, bis, type) ← forallMetaTelescope type
  let lhs := type.getArg! 1

  try
    for (id,v) in hint do
      xs[id]!.mvarId!.assignIfDefeq v
  catch _ =>
    trace[Meta.Tactic.fun_trans.discharge]    "failed to use `{← ppOrigin (.decl thmName)}` on `{e}`"
    return .none

  let extraArgsNum := e.getAppNumArgs - lhs.getAppNumArgs
  let e' := e.stripArgsN extraArgsNum
  let extraArgs := e.getAppArgsN extraArgsNum
  let .some r ← tryTheoremCore lhs xs bis proof type e' (.decl thmName) | return .none
  return (← r.addExtraArgs extraArgs)


#check Lean.indentExpr

def applyIdRule (funTransDecl : FunTransDecl) (e X : Expr) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "id case"

  let .some thms ← getLambdaTheorems funTransDecl.funTransName .id e.getAppNumArgs
    | trace[Meta.Tactic.fun_trans] "missing identity rule to prove `{← ppExpr e}`"
      return .continue

  for thm in thms do
    let .id id_X := thm.thmArgs | continue

    if let .some r ← tryTheoremWithHint e thm.thmName #[(id_X,X)] then
      return .visit r

  return .continue

def applyConstRule (funTransDecl : FunTransDecl) (e X y : Expr) : SimpM Simp.Step := do
  let .some thms ← getLambdaTheorems funTransDecl.funTransName .const e.getAppNumArgs
    | trace[Meta.Tactic.fun_trans] "missing const rule to prove `{← ppExpr e}`"
      return .continue

  for thm in thms do
    let .const id_X id_y := thm.thmArgs | continue

    if let .some r ← tryTheoremWithHint e thm.thmName #[(id_X,X), (id_y,y)] then
      return .visit r

  return .continue



def applyCompRule (funTransDecl : FunTransDecl) (e f g : Expr) : SimpM Simp.Step := do
  let .some thms ← getLambdaTheorems funTransDecl.funTransName .comp e.getAppNumArgs
    | trace[Meta.Tactic.fun_trans] "missing comp rule to prove `{← ppExpr e}`"
      return .continue

  for thm in thms do
    let .comp id_f id_g := thm.thmArgs | continue
    trace[Meta.Tactic.fun_trans] "trying comp theorem {thm.thmName}"
    if let .some r ← tryTheoremWithHint e thm.thmName #[(id_f,f),(id_g,g)] then
      return .visit r

  return .continue

def applyLetRule (funTransDecl : FunTransDecl) (e f g : Expr) : SimpM Simp.Step := do
  let .some thms ← getLambdaTheorems funTransDecl.funTransName .letE e.getAppNumArgs
    | trace[Meta.Tactic.fun_trans] "missing let rule to prove `{← ppExpr e}`"
      return .continue

  for thm in thms do
    let .letE id_f id_g := thm.thmArgs | continue

    if let .some r ← tryTheoremWithHint e thm.thmName #[(id_f,f),(id_g,g)] then
      return .visit r

  return .continue


def applyPiRule (funTransDecl : FunTransDecl) (e f : Expr) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "id case"
  return .continue


def letCase (funTransDecl : FunTransDecl) (e f : Expr) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "let case"

  let .lam xName xType (.letE yName yType yVal yBody _) xBi := f | return .continue

  let f := Expr.lam xName xType (.lam yName yType yBody .default) xBi
  let g := Expr.lam xName xType yVal .default

  applyLetRule funTransDecl e f g

def bvarAppCase (funTransDecl : FunTransDecl) (e : Expr) (fData : FunProp.FunctionData) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "bvar app case"
  return .continue

def fvarAppCase (funTransDecl : FunTransDecl) (e : Expr) (fData : FunProp.FunctionData) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "fvar app case"
  if let .some (f,g) ← fData.nontrivialDecomposition then
    return ← applyCompRule funTransDecl e f g
  return .continue

def constAppCase (funTransDecl : FunTransDecl) (e : Expr) (fData : FunProp.FunctionData) : SimpM Simp.Step := do
  trace[Meta.Tactic.fun_trans.step] "const app case on {← ppExpr e}"

  let .some funName ← fData.getFnConstName? | panic "fun_trans bug: incorrectly calling constAppCase!"

  let thms ← getTheoremsForFunction funName funTransDecl.funTransName e.getAppNumArgs fData.mainArgs

  trace[Meta.Tactic.fun_trans] "candidate theorems for {funName}: {thms.map fun thm => thm.thmName}"


  for thm in thms do
    trace[Meta.Tactic.fun_trans] "trying {thm.thmName}"

    if thm.form == .uncurried then
      if let .some (f',g') ← fData.nontrivialDecomposition then
         trace[Meta.Tactic.fun_trans] "succesfully decomposed"
         return ← applyCompRule funTransDecl e f' g'

    if let .some r ← tryTheoremWithHint e thm.thmName #[] then
      return .visit r

  return .continue


/-- Main `funProp` function. Returns proof of `e`. -/
@[export mathlib_fun_trans]
partial def funTransImpl (e : Expr) : SimpM Simp.Step := do

  let e ← instantiateMVars e

  let .some (funTransDecl, f) ← getFunTrans? e | return .continue

  trace[Meta.Tactic.fun_trans.step] s!"runing fun_trans on {← ppExpr e}"


  let f ← FunProp.funPropNormalizeFun f
  -- somehow normalize f
  -- that means unfold head functions like `id`, `Function.comp` or `HasUncurry.unucurry`

  -- bubble leading lets infront of function transformationx
  if f.isLet then
    return ← FunProp.letTelescope f fun xs b => do
      trace[Meta.Tactic.fun_trans.step] "moving let bindings out"
      let e' := e.setArg funTransDecl.funArgId b
      return .visit { expr := ← mkLambdaFVars xs e' }


  let .lam _xName xType xBody _xBi := f
    | throwError "fun_trans bug: function {← ppExpr f} is in invalid form"

  match xBody with
  | .bvar 0  => applyIdRule funTransDecl e xType
  | .letE .. => letCase funTransDecl e f
  | .lam  .. => applyPiRule funTransDecl e f
  | .mvar .. => funTransImpl e
  | xBody => do

    if ¬xBody.hasLooseBVars then
      return ← applyConstRule funTransDecl e xType xBody

    let fData ← FunProp.getFunctionData f

    match fData.fn with
    | .fvar id =>
      if id == fData.mainVar.fvarId!
      then bvarAppCase funTransDecl e fData
      else fvarAppCase funTransDecl e fData
    | .mvar .. => funTransImpl (← instantiateMVars e)
    | .const ..
    | .proj .. => constAppCase funTransDecl e fData
    | _ =>
      trace[Meta.Tactic.fun_trans.step] "unknown case, ctor: {fData.fn.ctorName}\n{e}"
      return .continue
