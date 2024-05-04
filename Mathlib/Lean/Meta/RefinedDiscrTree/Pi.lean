/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean.Meta.WHNF

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

The Pi type instances only applies when the domain is a `Type*`, and not a `Prop`.
However, there are cases in which the domain is a `Sort*` where we would still like to do these
reductions. So we ignore universe levels.

Not every instance that gives a function is a Pi type instance, for example for matrices
`A` and `B`, the coefficient `(A * B) i j` is not the same as `A i j * B i j`. Thus, to check
whether the instance is truly a Pi type instance, we unfold it to whnf, and check that the
function distributes as expected.

Another issue is the following:
`fun x => (a x)^(b x)` would be indexed as `λ, (* ^ *)`. But `fun x => x^2` would be indexed as
`(λ, #0)^2`. The problem is that depending on the instantiation of `b`, the exponent may or may not
depend on the bound variable `x`. Thus, in the case that the exponent depends on the bound variable,
but could avoid depending on it, we must index it with and without the distributed lambda.

A similar situation occurs in `fun [Ring α] => (1 + 2 : α)`, where the instance argument contains
the bound variable. In this case we never want to distribute the function.

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

/-- Reduce the Pi type instance to whnf, reducing inside of `numArgs` lambda binders. -/
private def unfoldPiInst (inst : Expr) (numArgs : Nat) : MetaM Expr := do
  let some e ← project? inst 0 | throwError "unable to project to field 1 in {inst}"
  forallBoundedTelescope (← inferType e) numArgs fun fvars _ => do
    let e ← whnf (mkAppN e fvars)
    mkLambdaFVars fvars e

private def absorbArgsUnOp (args : Array Expr) (idx : Nat) (type inst arg : Expr)
    (matchPiInst : Expr → Option Expr) (numArgs : Nat) : MetaM (Expr × Expr × Option Nat) := do
  if h : idx < args.size then
    let some inst := matchPiInst (← unfoldPiInst inst numArgs) | return (type, arg, some idx)
    let extraArg := args[idx]
    let .forallE _ _ body _ ← whnf type | throwFunctionExpected type
    let type := body.instantiate1 extraArg
    let inst := .app inst extraArg
    let arg  := .app arg extraArg
    absorbArgsUnOp args (idx+1) type inst arg matchPiInst numArgs
  else
    return (type, arg, none)
termination_by args.size - idx

private def absorbArgsBinOp (args : Array Expr) (idx : Nat) (type inst lhs rhs : Expr)
    (matchPiInst : Expr → Option Expr) (numArgs : Nat) :
    MetaM (Expr × Expr × Expr × Option Nat) := do
  if h : idx < args.size then
    let some inst := matchPiInst (← unfoldPiInst inst numArgs) | return (type, lhs, rhs, some idx)
    let extraArg := args[idx]
    let .forallE _ _ body _ ← whnf type | throwFunctionExpected type
    let type := body.instantiate1 extraArg
    let inst := .app inst extraArg
    let lhs  := .app lhs extraArg
    let rhs  := .app rhs extraArg
    absorbArgsBinOp args (idx+1) type inst lhs rhs matchPiInst numArgs
  else
    return (type, lhs, rhs, none)
termination_by args.size - idx

/-- Return true iff `e` must cointain a free variable which satisfies `p`,
no matter the instantiation of the metavariables. -/
@[inline] private def mustHaveAnyFVar (e : Expr) (p : FVarId → Bool) : Bool :=
  let rec @[specialize] visit (e : Expr) := if !e.hasFVar then false else
    match e with
    | .forallE _ d b _   => visit d || visit b
    | .lam _ d b _       => visit d || visit b
    | .mdata _ e         => visit e
    | .letE _ t v b _    => visit t || visit v || visit b
    | .app f a           => !f.getAppFn.isMVar && (visit a || visit f)
    | .proj _ _ e        => visit e
    | .fvar fvarId       => p fvarId
    | _                      => false
  visit e

/-- Return `true` if `e` contains the given free variable. -/
private def mustContainFVar (fvarId : FVarId) (e : Expr) : Bool :=
  mustHaveAnyFVar e (· == fvarId)


private def absorbLambdasUnOp (lambdas : List FVarId) (type arg : Expr)
    (otherArgs : Array Expr) :
    MetaM (Array (Expr × Expr × List FVarId)) := do
  match lambdas with
  | [] => return #[(type, arg, [])]
  | fvarId :: lambdas' =>
    let cannotAbsorb := otherArgs.any (·.containsFVar fvarId)
    let canNeverAbsorb := cannotAbsorb && otherArgs.any (mustContainFVar fvarId)
    if canNeverAbsorb then
      return #[(type, arg, lambdas)]
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let arg  := mkLam arg
    let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
    let result ← absorbLambdasUnOp lambdas' type arg otherArgs
    if cannotAbsorb then
      return result.push (type, arg, lambdas)
    else
      return result

private def absorbLambdasBinOp (lambdas : List FVarId) (type lhs rhs : Expr)
    (otherArgs : Array Expr) :
    MetaM (Array (Expr × Expr × Expr × List FVarId)) := do
  match lambdas with
  | [] => return #[(type, lhs, rhs, [])]
  | fvarId :: lambdas' =>
    let cannotAbsorb := otherArgs.any (·.containsFVar fvarId)
    let canNeverAbsorb := cannotAbsorb && otherArgs.any (mustContainFVar fvarId)
    if canNeverAbsorb then
      return #[(type, lhs, rhs, lambdas)]
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let lhs  := mkLam lhs
    let rhs  := mkLam rhs
    let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
    let result ← absorbLambdasBinOp lambdas' type lhs rhs otherArgs
    if cannotAbsorb then
      return result.push (type, lhs, rhs, lambdas)
    else
      return result

/-- Normalize an application of a constant with a Pi-type instance which distributes over
one argument. -/
def reduceUnOpAux (type inst arg : Expr) (lambdas : List FVarId) (args : Array Expr)
    (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr) (numArgs : Nat)
    (mk : Expr → Expr → Array (Option Expr)) :
    MetaM (Array (Array (Option Expr) × List FVarId)) := do
  let (type, arg, idx) ← absorbArgsUnOp args arity type inst arg matchPiInst numArgs
  if let some idx := idx then
    return #[(mk type arg ++ args[idx:].toArray.map some, lambdas)]
  (← absorbLambdasUnOp lambdas type arg otherArgs).mapM fun (type, arg, lambdas) =>
    return (mk type arg, lambdas)

/-- Normalize an application of a constant with a Pi-type instance which distributes over
two arguments that have the same type. -/
def reduceBinOpAux (type inst lhs rhs : Expr) (lambdas : List FVarId) (args : Array Expr)
    (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr) (numArgs : Nat)
    (mk : Expr → Expr → Expr → Array (Option Expr)) :
    MetaM (Array (Array (Option Expr) × List FVarId)) := do
  let (type, lhs, rhs, idx) ← absorbArgsBinOp args arity type inst lhs rhs matchPiInst numArgs
  if let some idx := idx then
    return #[(mk type lhs rhs ++ args[idx:].toArray.map some, lambdas)]
  (← absorbLambdasBinOp lambdas type lhs rhs otherArgs).mapM fun (type, lhs, rhs, lambdas) =>
    return (mk type lhs rhs, lambdas)


/-- Normalize an application if the head is `⁻¹` or `-`. -/
def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Array (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 2 then return none else some <$> do
  let type := args[0]
  let inst := args[1]
  etaExpand args type lambdas 3 fun args lambdas _ => do
    let arg := args[2]
    reduceUnOpAux type inst arg lambdas args #[inst] 3
      (fun
        | .lam _ _ (.lam _ _
          (mkApp6 (.const n' _) _ _ _ inst (.app (.bvar 2) (.bvar 0)) (.bvar 1))
          _) _ => if n' == n then inst else none
        | _ => none) 1
      (fun type arg => #[type, none, arg])

/-- Normalize an application if the head is `•` or `+ᵥ`. -/
def reduceHActOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Array (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 5 then return none else
  let mkApp3 (.const i _) α type inst := args[3] | return none
  let instH := match n with
    | `HVAdd.hVAdd => `instHVAdd
    | `HSMul.hSMul => `instHSMul
    | _ => unreachable!
  unless i == instH do return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let a := args[4]
    let arg := args[5]
    reduceUnOpAux type inst arg lambdas args #[inst, a] 6
      (fun
        | .lam _ _ (.lam _ _ (.lam _ _
          (mkApp6 (.const n' _) _ _ _ inst (.bvar 2) (.app (.bvar 1) (.bvar 0)))
          _) _) _ => if n' == n then inst else none
        | _ => none) 2
      (fun type arg => #[α, type, none, none, a, arg])

/-- Normalize an application if the head is `^`. -/
def reduceHPow (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Array (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 6 then return none else
  let mkApp3 (.const ``instHPow _) type β inst := args[3] | return none
  let arg := args[4]
  let exp := args[5]
  reduceUnOpAux type inst arg lambdas args #[inst, exp] 6
      (fun
        | .lam _ _ (.lam _ _ (.lam _ _
          (mkApp6 (.const ``HPow.hPow _) _ _ _ inst (.app (.bvar 2) (.bvar 0)) (.bvar 1))
          _) _) _ => inst
        | _ => none) 2
    (fun type arg => #[type, β, none, none, arg, exp])


/-- Normalize an application if the head is `+`, `*`, `-` or `/`. -/
def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId):
    MetaM (Option (Array (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 4 then return none else do
  let mkApp2 (.const i _) type inst := args[3] | return none
  let instH := match n with
    | ``HAdd.hAdd => ``instHAdd
    | ``HMul.hMul => ``instHMul
    | ``HSub.hSub => ``instHSub
    | ``HDiv.hDiv => ``instHDiv
    | _ => unreachable!
  unless i == instH do return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let lhs := args[4]
    let rhs := args[5]
    reduceBinOpAux type inst lhs rhs lambdas args #[inst] 6
      (fun
        | .lam _ _ (.lam _ _ (.lam _ _
          (mkApp6 (.const n' _) _ _ _ inst (.app (.bvar 2) (.bvar 0)) (.app (.bvar 1) (.bvar 0)))
          _) _) _ =>
          if n == n' then inst else none
        | _ => none) 2
      (fun type lhs rhs => #[type, type, none, none, lhs, rhs])

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
@[inline] def reducePi (e : Expr) (lambdas : List FVarId) :
    MetaM (Option (Name × Array (Array (Option Expr) × List FVarId))) := do
  if let .const n _ := e.getAppFn then
    match n with
    | ``Neg.neg
    |  `Inv.inv     => Option.map (n, ·) <$> reduceUnOp   n e.getAppArgs lambdas
    |  `HVAdd.hVAdd
    |  `HSMul.hSMul => Option.map (n, ·) <$> reduceHActOp n e.getAppArgs lambdas
    | ``HPow.hPow   => Option.map (n, ·) <$> reduceHPow     e.getAppArgs lambdas
    | ``HAdd.hAdd
    | ``HMul.hMul
    | ``HSub.hSub
    | ``HDiv.hDiv   => Option.map (n, ·) <$> reduceHBinOp n e.getAppArgs lambdas
    | _ => return none
  else
    return none
