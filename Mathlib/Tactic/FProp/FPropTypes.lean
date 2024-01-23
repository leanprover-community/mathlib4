/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean.Meta.Tactic.Simp.Types
import Std.Data.RBMap.Alter
import Std.Lean.Meta.DiscrTree
import Mathlib.Tactic.FProp.Meta

/-!
## `fprop` 

this file defines enviroment extension for `fprop`
-/


namespace Mathlib
open Lean Meta

namespace Meta.FProp


initialize registerTraceClass `Meta.Tactic.fprop.attr
initialize registerTraceClass `Meta.Tactic.fprop
initialize registerTraceClass `Meta.Tactic.fprop.step
initialize registerTraceClass `Meta.Tactic.fprop.unify
initialize registerTraceClass `Meta.Tactic.fprop.discharge
initialize registerTraceClass `Meta.Tactic.fprop.apply
initialize registerTraceClass `Meta.Tactic.fprop.cache


-- initialize registerTraceClass `Meta.Tactic.fprop.missing_rule
-- -- initialize registerTraceClass `Meta.Tactic.fprop.normalize_let
-- initialize registerTraceClass `Meta.Tactic.fprop.rewrite
-- initialize registerTraceClass `Meta.Tactic.fprop.discharge
-- initialize registerTraceClass `Meta.Tactic.fprop.unify
-- initialize registerTraceClass `Meta.Tactic.fprop.apply


/-- -/
structure Config where
  -- config

/-- -/
structure State where
  /-- Simp's cache is used as the `fprop` tactic is designed to be used inside of simp and utilize its cache -/
  cache        : Simp.Cache := {}

/-- -/
abbrev FPropM := ReaderT FProp.Config $ StateRefT FProp.State MetaM

/-- Result of `fprop`, it is a proof of function property `P f` and list of 
pending subgoals. These subgoals are meant to be solved by the user or passed to another automation.
-/
structure Result where
  proof : Expr
  subgoals : List MVarId



/-- FProp normal form of a function is of the form `fun x => b` where `b` is eta reduced.

In fprop normal form
```
fun x => f x
fun x => y + x
```

Not in fprop normal form
```
fun x y => f x y
HAdd.hAdd y
```-/
def fpropNormalizeFun (f : Expr) : MetaM Expr := do
  let f := f.consumeMData.eta
  let f ← 
    if f.isLambda 
    then pure f
    else do
      let X := (← inferType f).bindingDomain!
      pure (.lam `x X (f.app (.bvar 0)) default)


structure FunctionData where
  lctx : LocalContext
  insts : LocalInstances
  fn : Expr
  args : Array Mor.Arg
  mainVar : Expr   -- main variable
  mainArgs : ArraySet Nat -- indices of `args` that contain `mainVars`


def FunctionData.isConstantFun (f : FunctionData) : Bool := 
  if f.mainArgs.size = 0 && !f.fn.containsFVar f.mainVar.fvarId! then
    true 
  else
    false

def FunctionData.domainType (f : FunctionData) : MetaM Expr := 
  withLCtx f.lctx f.insts do
    inferType f.mainVar

def FunctionData.getFnConstName? (f : FunctionData) : MetaM (Option Name) := do

  match f.fn with
  | .const n _ => return n
  | .proj typeName idx _ => 
    let .some info := getStructureInfo? (← getEnv) typeName | return none
    let .some projName := info.getProjFn? idx | return none
    return projName
  | _ => return none

def getFunctionData (f : Expr) : MetaM FunctionData := do
  let f ← fpropNormalizeFun f 
  lambdaTelescope f fun xs b => do
    if xs.size ≠ 1 then
      throwError "fprop bug: invalid function {← ppExpr f}"

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


def FunctionData.toExpr (f : FunctionData) : MetaM Expr := do
  withLCtx f.lctx f.insts do
    let body := Mor.mkAppN f.fn f.args
    mkLambdaFVars #[f.mainVar] body

