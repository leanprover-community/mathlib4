/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init
import Lean.Meta.WHNF

/-!
# Reducing Pi instances for indexing in the RefinedDiscrTree

The function `Pi.reduce` reduces operations `+`, `-`, `*`, `/`, `⁻¹`, `+ᵥ`, `•`, `^`,
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

namespace Lean.Meta.RefinedDiscrTree.Pi

/-- Reduce the Pi type instance to whnf, reducing inside of `numArgs` lambda binders. -/
private def unfoldPiInst (inst : Expr) (numArgs : Nat) : MetaM Expr := do
  let some e ← project? inst 0 | throwError "unable to project to field 1 in {inst}"
  forallBoundedTelescope (← inferType e) numArgs fun fvars _ => do
    let e ← whnf (mkAppN e fvars)
    mkLambdaFVars fvars e

@[specialize] private def absorbArgsUnOp (args : Array Expr) (idx : Nat) (type inst arg : Expr)
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

@[specialize] private def absorbArgsBinOp (args : Array Expr) (idx : Nat) (type inst lhs rhs : Expr)
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
    | .forallE _ d b _ => visit d || visit b
    | .lam _ d b _     => visit d || visit b
    | .mdata _ e       => visit e
    | .letE _ t v b _  => visit t || visit v || visit b
    | .app f a         => !f.getAppFn.isMVar && (visit a || visit f)
    | .proj _ _ e      => visit e
    | .fvar fvarId     => p fvarId
    | _                => false
  visit e

/-- Return `true` if `e` contains the given free variable. -/
private def mustContainFVar (fvarId : FVarId) (e : Expr) : Bool :=
  mustHaveAnyFVar e (· == fvarId)


private def absorbLambdasUnOp (lambdas : List FVarId) (type arg : Expr)
    (otherArgs : Array Expr) : MetaM (List (Expr × Expr × List FVarId)) := do
  match lambdas with
  | [] => return [(type, arg, [])]
  | fvarId :: lambdas' =>
    let cannotAbsorb := otherArgs.any (·.containsFVar fvarId)
    let canNeverAbsorb := cannotAbsorb && otherArgs.any (mustContainFVar fvarId)
    if canNeverAbsorb then
      return [(type, arg, lambdas)]
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let arg  := mkLam arg
    let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
    if cannotAbsorb then
      return (type, arg, lambdas) :: (← absorbLambdasUnOp lambdas' type arg otherArgs)
    else
      absorbLambdasUnOp lambdas' type arg otherArgs

private def absorbLambdasBinOp (lambdas : List FVarId) (type lhs rhs : Expr)
    (otherArgs : Array Expr) : MetaM (List (Expr × Expr × Expr × List FVarId)) := do
  match lambdas with
  | [] => return [(type, lhs, rhs, [])]
  | fvarId :: lambdas' =>
    let cannotAbsorb := otherArgs.any (·.containsFVar fvarId)
    let canNeverAbsorb := cannotAbsorb && otherArgs.any (mustContainFVar fvarId)
    if canNeverAbsorb then
      return [(type, lhs, rhs, lambdas)]
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let lhs  := mkLam lhs
    let rhs  := mkLam rhs
    let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
    if cannotAbsorb then
      return (type, lhs, rhs, lambdas) :: (← absorbLambdasBinOp lambdas' type lhs rhs otherArgs)
    else
      absorbLambdasBinOp lambdas' type lhs rhs otherArgs

/-- Normalize an application of a constant with a Pi-type instance which distributes over
one argument. -/
@[specialize] def reduceUnOpAux (type inst arg : Expr) (lambdas : List FVarId) (args : Array Expr)
    (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr) (numArgs : Nat)
    (mk : Expr → Expr → Array (Option Expr)) :
    MetaM (List (Array (Option Expr) × List FVarId)) := do
  let (type, arg, idx) ← absorbArgsUnOp args arity type inst arg matchPiInst numArgs
  match idx with
  | some idx => return [(mk type arg ++ args[idx:].toArray.map some, lambdas)]
  | none =>
    (← absorbLambdasUnOp lambdas type arg otherArgs).mapM fun (type, arg, lambdas) =>
      return (mk type arg, lambdas)

/-- Normalize an application of a constant with a Pi-type instance which distributes over
two arguments that have the same type. -/
@[specialize] def reduceBinOpAux (type inst lhs rhs : Expr) (lambdas : List FVarId)
    (args : Array Expr) (otherArgs : Array Expr) (arity : Nat) (matchPiInst : Expr → Option Expr)
    (numArgs : Nat) (mk : Expr → Expr → Expr → Array (Option Expr)) :
    MetaM (List (Array (Option Expr) × List FVarId)) := do
  let (type, lhs, rhs, idx) ← absorbArgsBinOp args arity type inst lhs rhs matchPiInst numArgs
  match idx with
  | some idx => return [(mk type lhs rhs ++ args[idx:].toArray.map some, lambdas)]
  | none =>
    (← absorbLambdasBinOp lambdas type lhs rhs otherArgs).mapM fun (type, lhs, rhs, lambdas) =>
      return (mk type lhs rhs, lambdas)

/-- Introduce new lambdas by η-expansion to reach the required number of arguments. -/
@[specialize]
private def etaExpand {α} (args : Array Expr) (type : Expr) (lambdas : List FVarId) (arity : Nat)
    (k : (args : Array Expr) → List FVarId → (arity ≤ args.size) → MetaM α) : MetaM α  := do
  if h : args.size < arity then
    withLocalDeclD `_η type fun fvar =>
      etaExpand (args.push fvar) type (fvar.fvarId! :: lambdas) arity k
  else
    k args lambdas (by omega)

@[inline] def app6? (fName : Name) (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity fName 6 then
    some (e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

def lambdaBody? (n : Nat) (e : Expr) : Option Expr :=
match n, e with
| 0, e => some e
| n+1, .lam _ _ b _ => lambdaBody? n b
| _, _ => none

/-- Normalize an application if the head is `⁻¹` or `-`. -/
def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 2 then return none else some <$> do
  let type := args[0]
  let inst := args[1]
  etaExpand args type lambdas 3 fun args lambdas _ => do
    let arg := args[2]
    reduceUnOpAux type inst arg lambdas args #[inst] 3
      (lambdaBody? 2 >=> app6? n >=> fun (inst, f, b) =>
        if (b == .bvar 1 && f == .app (.bvar 2) (.bvar 0)) then inst else none) 1
      (fun type arg => #[type, none, arg])

/-- Normalize an application if the head is `•` or `+ᵥ`. -/
def reduceHActOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 5 then return none else
  let rec instH := match n with
    | `HVAdd.hVAdd => `instHVAdd
    | `HSMul.hSMul => `instHSMul
    | _ => unreachable!
  let some (α, type, inst) := args[3].app3? instH | return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let a := args[4]
    let arg := args[5]
    reduceUnOpAux type inst arg lambdas args #[inst, a] 6
      (lambdaBody? 3 >=> app6? n >=> fun (inst, f, b) =>
        if (b == .bvar 1 && f == .app (.bvar 2) (.bvar 0)) then inst else none) 2
      (fun type arg => #[α, type, none, none, a, arg])

/-- Normalize an app lication if the head is `^`. -/
def reduceHPow (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 6 then return none else
  let some (type, β, inst) := args[3].app3? ``instHPow | return none
  let arg := args[4]
  let exp := args[5]
  reduceUnOpAux type inst arg lambdas args #[inst, exp] 6
      (lambdaBody? 3 >=> app6? ``HPow.hPow >=> fun (inst, f, b) =>
        if (b == .bvar 1 && f == .app (.bvar 2) (.bvar 0)) then inst else none) 2
    (fun type arg => #[type, β, none, none, arg, exp])


/-- Normalize an application if the head is `+`, `*`, `-` or `/`. -/
def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId):
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 4 then return none else do
  let rec instH := match n with
    | ``HAdd.hAdd => ``instHAdd
    | ``HMul.hMul => ``instHMul
    | ``HSub.hSub => ``instHSub
    | ``HDiv.hDiv => ``instHDiv
    | _ => unreachable!
  let some (type, inst) := args[3].app2? instH | return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let lhs := args[4]
    let rhs := args[5]
    reduceBinOpAux type inst lhs rhs lambdas args #[inst] 6
      (lambdaBody? 3 >=> app6? n >=> fun (inst, f, b) =>
        if (b == .bvar 1 && f == .app (.bvar 2) (.bvar 0)) then inst else none) 2
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
def reduce (e : Expr) (lambdas : List FVarId) :
    MetaM (Option (Name × List (Array (Option Expr) × List FVarId))) := do
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

end Lean.Meta.RefinedDiscrTree.Pi
