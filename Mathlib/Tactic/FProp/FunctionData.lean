/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Mathlib.Tactic.FProp.Mor

/-!
## `fprop` data structure holding information about a function

`FunctionData` holds data about function in the form `fun x => f x₁ ... xₙ`.
-/

namespace Mathlib
open Lean Meta

namespace Meta.FProp


/-- fprop-normal form of a function is of the form `fun x => f x₁ ... xₙ`.

Throws and error if function can't be turned into fprop-normal form.

Examples:
In fprop-normal form
```
fun x => f x
fun x => y + x
```

Not in fprop-normal form
```
fun x y => f x y
HAdd.hAdd y
```-/
def fpropNormalizeFun (f : Expr) : MetaM Expr := do
  let f := f.consumeMData.eta
  lambdaTelescope f fun xs _ => do

    if xs.size = 0 then
      let X := (← inferType f).bindingDomain!
      return (.lam `x X (f.app (.bvar 0)) default)
    else
      return f


/-- Structure storing parts of a function in fprop-normal form. -/
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

/-- Is `f` a constant function? -/
def FunctionData.isConstantFun (f : FunctionData) : Bool :=
  if f.mainArgs.size = 0 && !f.fn.containsFVar f.mainVar.fvarId! then
    true
  else
    false

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


/-- Get `FunctionData` for `f`. Throws if `f` can be put into fprop-normal form. -/
def getFunctionData (f : Expr) : MetaM FunctionData := do
  let f ← fpropNormalizeFun f
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

/-- If `f` is in the form `fun x => @DFunLike.coe F α β self f x₁ ... xₙ` return the number of
arguments of `DFunLike.coe` i.e. `n + 5`. -/
def FunctionData.getCoeAppNumArgs? (f : FunctionData) : Option Nat :=

  if f.fn.isConstOf ``DFunLike.coe then
    return f.args.size
  else Id.run do

    for i' in [0:f.args.size] do
      let i := (f.args.size - i') - 1
      if f.args[i]!.coe.isSome then
        return .some (i' + 6)

    return none

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

    -- todo: support case when `fn` contains `x`
    --       but can we have non trivial decomposition when `fn` contains `x`?
    if fn.containsFVar xId then
      return none

    let mut yVals : Array Expr := #[]
    let mut yVars : Array Expr := #[]

    for argId in fData.mainArgs do
      let yVal := args[argId]!

      let yVal' := yVal.expr
      let yId ← withLCtx lctx insts mkFreshFVarId
      let yType ← withLCtx lctx insts (inferType yVal')
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
