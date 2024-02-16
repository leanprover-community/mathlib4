/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Std.Lean.Expr
import Mathlib.Tactic.FunProp.MorExt

/-!
## `funProp` data structure holding information about a function

`FunctionData` holds data about function in the form `fun x => f x₁ ... xₙ`.
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp


/-- Structure storing parts of a function in funProp-normal form. -/
structure FunctionData where
  /-- local context where `mainVar` exists -/
  lctx : LocalContext
  /-- local instances -/
  insts : LocalInstances
  /-- main function -/
  fn : Expr
  /-- applied function arguments -/
  args : Array Mor.Arg
  /-- main variable -/
  mainVar : Expr
  /-- indices of `args` that contain `mainVars` -/
  mainArgs : Array Nat

/-- Turn function data back to expression. -/
def FunctionData.toExpr (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

/-- Is `f` an indentity function? -/
def FunctionData.isIdentityFun (f : FunctionData) : Bool :=
  (f.args.size = 0 && f.fn == f.mainVar)

/-- Is `f` a constant function? -/
def FunctionData.isConstantFun (f : FunctionData) : Bool :=
  ((f.mainArgs.size = 0) && !(f.fn.containsFVar f.mainVar.fvarId!))

/-- Domain type of `f`. -/
def FunctionData.domainType (f : FunctionData) : MetaM Expr :=
  withLCtx f.lctx f.insts do
    inferType f.mainVar

/-- Is head function of `f` a constant?

If the head of `f` is a projection return the name of corresponding projection function. -/
def FunctionData.getFnConstName? (f : FunctionData) : MetaM (Option Name) := do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ =>
    let .some info := getStructureInfo? (← getEnv) typeName | return none
    let .some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none


/-- Get `FunctionData` for `f`. Throws if `f` can't be put into funProp-normal form. -/
def getFunctionData (f : Expr) : MetaM FunctionData := do
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i.1 else none)
        |>.filterMap id

      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }

inductive MaybeFunctionData where
  /-- Can't generate function data as function body has let binder. -/
  | letE (f : Expr)
  /-- Can't generate function data as function body has lambda binder. -/
  | lam (f : Expr)
  /-- Function data has been successfully generated. -/
  | data (fData : FunctionData)

/-- Get `FunctionData` for `f`. -/
def getFunctionData? (f : Expr)
    (unfoldPred : Name → Bool := fun _ => false) (cfg : WhnfCoreConfig := {}) :
    MetaM MaybeFunctionData := do

  let unfold := fun e : Expr =>
    if let .some n := e.getAppFn'.constName? then
      pure (unfoldPred n)
    else
      pure false

  let .forallE xName xType _ _ ← inferType f | throwError "fun_prop bug: function expected"
  withLocalDeclD xName xType fun x => do
    let fx' ← Mor.whnfPred (f.app x) unfold cfg
    let f' ← mkLambdaFVars #[x] fx'
    match fx' with
    | .letE .. => return .letE f'
    | .lam  .. => return .lam f'
    | _ => return .data (← getFunctionData f')


inductive MorApplication where
  | underApplied | exact | overApplied | none

/--  -/
def FunctionData.isMorApplication (f : FunctionData) : MetaM MorApplication := do
  if let .some name := f.fn.constName? then
    if ← Mor.isMorCoeName name then
      let info ← getConstInfo name
      let arity := info.type.forallArity
      match compare arity f.args.size with
      | .eq => return .exact
      | .lt => return .overApplied
      | .gt => return .underApplied
  match f.args.size with
  | 0 => return .none
  | _ =>
    let n := f.args.size
    if f.args[n-1]!.coe.isSome then
      return .exact
    else if f.args.any (fun a => a.coe.isSome) then
      return .overApplied
    else
      return .none


/-- Decomposes `fun x => f y₁ ... yₙ` into `(fun g => g yₙ) ∘ (fun x y => f y₁ ... yₙ₋₁ y)`

Returns none if:
  - `n=0`
  - `yₙ` contains `x`
  - `n=1` and `(fun x y => f y)` is identity function i.e. `x=f` -/
def FunctionData.peeloffArgDecomposition (fData : FunctionData) : MetaM (Option (Expr × Expr)) := do
  unless fData.args.size > 0 do return none
  withLCtx fData.lctx fData.insts do
    let n := fData.args.size
    let x := fData.mainVar
    let yₙ := fData.args[n-1]!

    if yₙ.expr.containsFVar x.fvarId! then
      return none

    if fData.args.size = 1 &&
       fData.mainVar == fData.fn then
      return none

    let gBody' := Mor.mkAppN fData.fn fData.args[:n-1]
    let gBody' := if let .some coe := yₙ.coe then coe.app gBody' else gBody'
    let g' ← mkLambdaFVars #[x] gBody'
    let f' := Expr.lam `f (← inferType gBody') (.app (.bvar 0) (yₙ.expr)) default
    return (f',g')


/-- Decompose function `f = (← fData.toExpr)` into composition of two functions.

Returns none if the decomposition would produce identity function. -/
def FunctionData.nontrivialDecomposition (fData : FunctionData) : MetaM (Option (Expr × Expr)) := do

    let mut lctx := fData.lctx
    let insts := fData.insts

    let x := fData.mainVar
    let xId := x.fvarId!
    let xName ← withLCtx lctx insts xId.getUserName

    let fn := fData.fn
    let mut args := fData.args

    if fn.containsFVar xId then
      return ← fData.peeloffArgDecomposition

    let mut yVals : Array Expr := #[]
    let mut yVars : Array Expr := #[]

    for argId in fData.mainArgs do
      let yVal := args[argId]!

      let yVal' := yVal.expr
      let yId ← withLCtx lctx insts mkFreshFVarId
      let yType ← withLCtx lctx insts (inferType yVal')
      if yType.containsFVar fData.mainVar.fvarId! then
        return none
      lctx := lctx.mkLocalDecl yId (xName.appendAfter (toString argId)) yType
      let yVar := Expr.fvar yId
      yVars := yVars.push yVar
      yVals := yVals.push yVal'
      args := args.set! argId ⟨yVar, yVal.coe⟩

    let g  ← withLCtx lctx insts do
      mkLambdaFVars #[x] (← mkProdElem yVals)
    let f ← withLCtx lctx insts do
      (mkLambdaFVars yVars (Mor.mkAppN fn args))
      >>=
      mkUncurryFun yVars.size

    -- check if is non-triviality
    let f' ← fData.toExpr
    if (← isDefEq f' f) || (← isDefEq f' g) then
      return none

    return (f, g)
