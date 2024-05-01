/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean.Meta.AppBuilder

/-!
# Reducing Pi instances for indexing in the RefinedDiscrTree

The function `reducePi` reduces operations `+`, `-`, `*`, `/`, `⁻¹`, `+ᵥ`, `•`, `^`,
according to the following reductions:
- η-expand: increase the number of arguments in case of under application.
  For example `HAdd.hAdd a` is turned into `fun x => a + x`.
- Absorbing arguments: whenever a pi instance is over applied, we unfold the constant.
  For example `(f + g) x` is turned into `f x + g x`.
- Absorbing lambdas: lambdas in front of the constant can be moved inside.
  For example `fun x => x + 1` is turned into `(fun x => x) + (fun x => 1)`.

-/

open Lean Meta

namespace Lean.Meta.RefinedDiscrTree

/-- Introduce new lambdas by η-expansion to reach the required number of arguments. -/
@[specialize]
private def etaExpand {α} (args : Array Expr) (type : Expr) (lambdas : List FVarId) (arity : Nat)
    (k : (args : Array Expr) → List FVarId → (arity ≤ args.size) → MetaM α) : MetaM α  := do
  if h : args.size < arity then
    withLocalDeclD `_η type fun fvar =>
      etaExpand (args.push fvar) type (fvar.fvarId! :: lambdas) arity k
  else
    k args lambdas (by omega)
termination_by arity - args.size


private def absorbArgsUnOp (args : Array Expr) (idx : Nat) (inst arg : Expr)
    (matchPiInst : Expr → Option Expr) : MetaM (Expr × Expr × Option Nat) := do
  if h : idx < args.size then
    let some inst := matchPiInst (← whnfR inst) | return (inst, arg, some idx)
    let extraArg := args[idx]
    let inst := .app inst extraArg
    let arg  := .app arg extraArg
    absorbArgsUnOp args (idx+1) inst arg matchPiInst
  else
    return (inst, arg, none)
termination_by args.size - idx

private def absorbArgsBinOp (args : Array Expr) (idx : Nat) (inst lhs rhs : Expr)
    (matchPiInst : Expr → Option Expr) : MetaM (Expr × Expr × Expr × Option Nat) := do
  if h : idx < args.size then
    let some inst := matchPiInst (← whnfR inst) | return (inst, lhs, rhs, some idx)
    let extraArg := args[idx]
    let inst := .app inst extraArg
    let lhs  := .app lhs extraArg
    let rhs  := .app rhs extraArg
    absorbArgsBinOp args (idx+1) inst lhs rhs matchPiInst
  else
    return (inst, lhs, rhs, none)
termination_by args.size - idx

private def absorbLambdasUnOp (lambdas : List FVarId) (inst arg : Expr)
    (otherArgs : Array Expr) (mkPiInst : Expr → MetaM Expr) :
    MetaM (Expr × Expr × List FVarId) := do
  match lambdas with
  | [] => return (inst, arg, [])
  | fvarId :: lambdas' =>
    if otherArgs.any (·.containsFVar fvarId) then
      return (inst, arg, lambdas)
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let inst := mkLam inst
    let arg  := mkLam arg
    absorbLambdasUnOp lambdas' (← mkPiInst inst) arg otherArgs mkPiInst

private def absorbLambdasBinOp (lambdas : List FVarId) (inst lhs rhs : Expr)
    (otherArgs : Array Expr) (mkPiInst : Expr → MetaM Expr) :
    MetaM (Expr × Expr × Expr × List FVarId) := do
  match lambdas with
  | [] => return (inst, lhs, rhs, [])
  | fvarId :: lambdas' =>
    if otherArgs.any (·.containsFVar fvarId) then
      return (inst, lhs, rhs, lambdas)
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let inst := mkLam inst
    let lhs  := mkLam lhs
    let rhs  := mkLam rhs
    absorbLambdasBinOp lambdas' (← mkPiInst inst) lhs rhs otherArgs mkPiInst

/-- Normalize an application of a constant with a Pi-type instance which distributes over
one argument. -/
def reduceUnOpAux (inst arg : Expr) (lambdas : List FVarId) (args : Array Expr)
    (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr)
    (mkPiInst : Expr → MetaM Expr)
    (mk : Expr → Expr → MetaM Expr) : MetaM (Expr × List FVarId) := do
  let (inst, arg, idx) ← absorbArgsUnOp args arity inst arg matchPiInst
  if let some idx := idx then
    return (mkAppN (← mk inst arg) (args[idx:]), lambdas)
  let (inst, arg, lambdas) ← absorbLambdasUnOp lambdas inst arg otherArgs mkPiInst
  return (← mk inst arg, lambdas)

/-- Normalize an application of a constant with a Pi-type instance which distributes over
two arguments that have the same type. -/
def reduceBinOpAux (inst lhs rhs : Expr) (lambdas : List FVarId) (args : Array Expr)
    (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr)
    (mkPiInst : Expr → MetaM Expr)
    (mk : Expr → Expr → Expr → MetaM Expr) : MetaM (Expr × List FVarId) := do
  let (inst, lhs, rhs, idx) ← absorbArgsBinOp args arity inst lhs rhs matchPiInst
  if let some idx := idx then
    return (mkAppN (← mk inst lhs rhs) (args[idx:]), lambdas)
  let (inst, lhs, rhs, lambdas) ← absorbLambdasBinOp lambdas inst lhs rhs otherArgs mkPiInst
  return (← mk inst lhs rhs, lambdas)


/-- Normalize an application if the head is `⁻¹` or `-`. -/
def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × List FVarId)) := do
  let instPi := match n with
    | ``Neg.neg => `Pi.instNeg
    |  `Inv.inv => `Pi.instInv
    | _ => unreachable!
  if h : args.size < 2 then return none else some <$> do
  let type := args[0]
  let inst := args[1]
  etaExpand args type lambdas 3 fun args lambdas _ => do
    let arg := args[2]
    reduceUnOpAux inst arg lambdas args #[inst] 3
      (fun
        | mkApp3 (.const i _) _ _ inst => if i == instPi then some inst else none
        | _ => none)
      (fun inst => mkAppOptM instPi #[none, none, inst])
      (fun inst arg => mkAppOptM n #[none, inst, arg])

/-- Normalize an application if the head is `•` or `+ᵥ`. -/
def reduceHActOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × List FVarId)) := do
  let (instH, instPi) := match n with
    | `HVAdd.hVAdd => (`instHVAdd, `Pi.instVAdd)
    | `HSMul.hSMul => (`instHSMul, `Pi.instSMul)
    | _ => unreachable!
  if h : args.size < 5 then return none else
  let mkApp3 (.const i _) _ type inst := args[3] | return none
  unless i == instH do return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let a := args[4]
    let arg := args[5]
    reduceUnOpAux inst arg lambdas args #[inst, a] 6
      (fun
        | mkApp4 (.const i _) _ _ _ inst => if i == instPi then some inst else none
        | _ => none)
      (fun inst => mkAppOptM instPi #[none, none, none, inst])
      (fun inst arg => do
        mkAppOptM n #[none, none, none, ← mkAppOptM instH #[none, none, inst], a, arg])

/-- Normalize an application if the head is `^`. -/
def reduceHPow (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × List FVarId)) := do
  if h : args.size < 6 then return none else
  let mkApp3 (.const ``instHPow _) _ _ inst := args[3] | return none
  let arg := args[4]
  let exp := args[5]
  reduceUnOpAux inst arg lambdas args #[inst, exp] 6
    (fun
      | mkApp4 (.const `Pi.instPow _) _ _ _ inst => some inst
      | _ => none)
    (fun inst => mkAppOptM `Pi.instPow #[none, none, none, inst])
      (fun inst arg => do
        mkAppOptM n #[none, none, none, ← mkAppOptM ``instHPow #[none, none, inst], arg, exp])


/-- Normalize an application if the head is `+`, `*`, `-` or `/`. -/
def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × List FVarId)) := do
  let (instH, instPi) := match n with
    | ``HAdd.hAdd => (``instHAdd, `Pi.instAdd)
    | ``HMul.hMul => (``instHMul, `Pi.instMul)
    | ``HSub.hSub => (``instHSub, `Pi.instSub)
    | ``HDiv.hDiv => (``instHDiv, `Pi.instDiv)
    | _ => unreachable!
  if h : args.size < 4 then return none else do
  let mkApp2 (.const i _) type inst := args[3] | return none
  unless i == instH do return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let lhs := args[4]
    let rhs := args[5]
    reduceBinOpAux inst lhs rhs lambdas args #[inst] 6
      (fun
        | mkApp3 (.const i _) _ _ inst => if i == instPi then some inst else none
        | _ => none)
      (fun inst => mkAppOptM instPi #[none, none, inst])
      (fun inst lhs rhs => do
        mkAppOptM n #[none, none, none, ← mkAppOptM instH #[none, inst], lhs, rhs])

/--
Normalize an application if the head is any of `+`, `-`, `*`, `/`, `⁻¹`, `+ᵥ`, `•`, `^`.
We assume that any lambda's at the head of the expression have already been introduced as
free variables, and they can be specified with a list of these free variables.
The order of the free variables is inner to outer, so `fun a b => ..` corresponds to `[b, a]`.

We apply the following reductions whenever possible:
- η-expand: increase the number of arguments in case of under application.
  For example `HAdd.hAdd a` is turned into `fun x => a + x`.
- Absorbing arguments: whenever a pi instance is over applied, we unfold the constant.
  For example `(f + g) x` is turned into `f x + g x`.
- Absorbing lambdas: lambdas in front of the constant can be moved inside.
  For example `fun x => x + 1` is turned into `(fun x => x) + (fun x => 1)`.
-/
def reducePi (e : Expr) (lambdas : List FVarId) : MetaM (Expr × List FVarId) := do
  if let .const n _ := e.getAppFn then
    match n with
    | ``Neg.neg
    |  `Inv.inv     => if let some result ← reduceUnOp   n e.getAppArgs lambdas then return result
    |  `HVAdd.hVAdd
    |  `HSMul.hSMul => if let some result ← reduceHActOp n e.getAppArgs lambdas then return result
    | ``HPow.hPow   => if let some result ← reduceHPow   n e.getAppArgs lambdas then return result
    | ``HAdd.hAdd
    | ``HMul.hMul
    | ``HSub.hSub
    | ``HDiv.hDiv   => if let some result ← reduceHBinOp n e.getAppArgs lambdas then return result
    | _ => pure ()
  return (e, lambdas)
