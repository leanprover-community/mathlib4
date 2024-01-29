/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean

import Mathlib.Tactic.FProp.ArraySet
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

    if xs.size > 1 then
      throwError "fprop bug: can't transform `{← ppExpr f}` to fprop-normal form"

    if xs.size = 0 then
      let X := (← inferType f).bindingDomain!
      return (.lam `x X (f.app (.bvar 0)) default)
    else
      return f


/-- Structure storing parts of a function in fprop-normal form. -/
structure FunctionData where
  lctx : LocalContext
  insts : LocalInstances
  fn : Expr
  args : Array Mor.Arg
  /-- main variable -/
  mainVar : Expr
  /-- indices of `args` that contain `mainVars` -/
  mainArgs : ArraySet Nat


/-- Get `FunctionData` for `f`. Throws if `f` can be put into fprop-normal form. -/
def getFunctionData (f : Expr) : MetaM FunctionData := do
  let f ← fpropNormalizeFun f
  lambdaTelescope f fun xs b => do

    let xId := xs[0]!.fvarId!

    Mor.withApp b fun fn args => do

      let mainArgs := args
        |>.mapIdx (fun i ⟨arg,_⟩ => if arg.containsFVar xId then some i.1 else none)
        |>.filterMap id
        |>.toArraySet

      return {
        lctx := ← getLCtx
        insts := ← getLocalInstances
        fn := fn
        args := args
        mainVar := xs[0]!
        mainArgs := mainArgs
      }

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



