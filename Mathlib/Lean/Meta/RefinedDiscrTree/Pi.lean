/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Algebra.Group.Operations
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

namespace Lean.Meta.RefinedDiscrTree

/-- Reduce the Pi type instance to whnf, reducing inside of `numArgs` lambda binders. -/
private def unfoldPiInst (inst : Expr) (numInstArgs : Nat) : MetaM Expr := do
  let some e ← project? inst 0 | throwError "unable to project to field 1 in {inst}"
  forallBoundedTelescope (← inferType e) numInstArgs fun fvars _ => do
    let e ← whnf (mkAppN e fvars)
    mkLambdaFVars fvars e

/--
Reduce an over-application, by distributing it over 1 argument.
- `(- f) xs` => `- (f xs)`
- `(f ^ n) xs` => `(f xs) ^ n`
- `(f + g) xs` => `f xs + g xs`
-/
@[specialize] private def absorbArgs (allArgs : Array Expr) (idx : Nat)
    (type inst : Expr) (args : List Expr) (matchPiInst : Expr → Option Expr) (numInstArgs : Nat) :
    MetaM (Expr × List Expr × Option Nat) := do
  if h : idx < allArgs.size then
    let some inst := matchPiInst (← unfoldPiInst inst numInstArgs) | return (type, args, some idx)
    let extraArg := allArgs[idx]
    let .forallE _ _ body _ ← whnf type | throwFunctionExpected type
    let type := body.instantiate1 extraArg
    let inst := .app inst extraArg
    let args := args.map (Expr.app · extraArg)
    absorbArgs allArgs (idx+1) type inst args matchPiInst numInstArgs
  else
    return (type, args, none)
termination_by allArgs.size - idx

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

/--
Change a lambda expression by distributing it over `args`.
- `fun xs => - a` => `- (fun xs => a)`
- `fun xs => a ^ n` => `(fun xs => a) ^ n`
- `fun xs => a + b` => `(fun xs => a) + (fun xs => b)`

Note: we return a `List` since this can have multiple results.
-/
private def absorbLambdas (lambdas : List FVarId) (type : Expr) (args : List Expr)
    (otherArgs : Array Expr) : MetaM (List (Expr × List Expr × List FVarId)) := do
  match lambdas with
  | [] => return [(type, args, [])]
  | fvarId :: lambdas' =>
    /-
    When `otherArgs` contains `fvarId`, then distributing the lambda would cause
    `fvarId` to be outside the lambda scope.

    But for the benefit of the doubt, we still allow the lambda to be distributed if
    under some metavariable assignment `fvarId` can disappear.
    -/
    let cannotAbsorb := otherArgs.any (·.containsFVar fvarId)
    let canNeverAbsorb := cannotAbsorb && otherArgs.any (mustContainFVar fvarId)
    if canNeverAbsorb then
      return [(type, args, lambdas)]
    let decl ← fvarId.getDecl
    let mkLam e := .lam decl.userName decl.type (e.abstract #[.fvar fvarId]) decl.binderInfo
    let args  := args.map mkLam
    let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
    if cannotAbsorb then
      return (type, args, lambdas) :: (← absorbLambdas lambdas' type args otherArgs)
    else
      absorbLambdas lambdas' type args otherArgs

/--
Normalize an application of a constant with a Pi-type instance which distributes,
by distributing over-applied arguments and/or distributing all lambdas.

Note: we return a `List` since this can have multiple results.
-/
@[specialize] private def reduceAux (type inst : Expr) (args : List Expr) (lambdas : List FVarId)
    (allArgs : Array Expr) (otherArgs : Array Expr) (arity numInstArgs : Nat)
    (matchPiInst : Expr → Option Expr) (mk : Expr → List Expr → Array (Option Expr)) :
    MetaM (List (Array (Option Expr) × List FVarId)) := do
  let (type, args, idx) ← absorbArgs allArgs arity type inst args matchPiInst numInstArgs
  match idx with
  | some idx => return [(mk type args ++ allArgs[idx:].toArray.map some, lambdas)]
  | none =>
    (← absorbLambdas lambdas type args otherArgs).mapM fun (type, args, lambdas) =>
      return (mk type args, lambdas)


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

@[inline] private def app6? (fName : Name) (e : Expr) : Option (Expr × Expr × Expr) :=
  if e.isAppOfArity fName 6 then
    some (e.appFn!.appFn!.appArg!, e.appFn!.appArg!, e.appArg!)
  else
    none

private def lambdaBody? (n : Nat) (e : Expr) : Option Expr :=
match n, e with
| 0, e => some e
| n+1, .lam _ _ b _ => lambdaBody? n b
| _, _ => none

/-- Normalize an application if the head is `⁻¹` or `-`. -/
private def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 2 then return none else some <$> do
  let type := args[0]
  let inst := args[1]
  etaExpand args type lambdas 3 fun args lambdas _ => do
    let arg := args[2]
    reduceAux type inst [arg] lambdas args #[inst] 3 1
      (lambdaBody? 2 >=> (·.app3? n) >=> fun (_, inst, a) =>
        -- check for `fun a x => -a x` or `fun a x => (a x)⁻¹`
        if (a == .app (.bvar 1) (.bvar 0)) then inst else none)
      (fun
        | type, [arg] => #[type, none, arg]
        | _, _ => unreachable! )

/-- Normalize an application if the head is `•` or `+ᵥ`. -/
private def reduceHActOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 5 then return none else
  let rec instH := match n with
    | ``HVAdd.hVAdd => ``instHVAdd
    | ``HSMul.hSMul => ``instHSMul
    | _ => unreachable!
  let some (α, type, inst) := args[3].app3? instH | return none
  etaExpand args type lambdas 6 fun args lambdas _ => do
    let a := args[4]
    let arg := args[5]
    reduceAux type inst [arg] lambdas args #[inst, a] 6 2
      (lambdaBody? 3 >=> app6? n >=> fun (inst, a, b) =>
        -- check for `fun a b x => a • b x` or `fun a b x => a +ᵥ b x`
        if (a == .bvar 2) && b == .app (.bvar 1) (.bvar 0) then inst else none)
      (fun
        | type, [arg] => #[α, type, none, none, a, arg]
        | _, _ => unreachable!)

/-- Normalize an application if the head is `^`. -/
private def reduceHPow (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (List (Array (Option Expr) × List FVarId))) := withDefault do
  if h : args.size < 6 then return none else
  let some (type, β, inst) := args[3].app3? ``instHPow | return none
  let arg := args[4]
  let exp := args[5]
  reduceAux type inst [arg] lambdas args #[inst, exp] 6 2
      (lambdaBody? 3 >=> app6? ``HPow.hPow >=> fun (inst, a, b) =>
        -- check for `fun a b x => a x ^ b`
        if (a == .app (.bvar 2) (.bvar 0) && b == .bvar 1) then inst else none)
    (fun
      | type, [arg] => #[type, β, none, none, arg, exp]
      | _, _ => unreachable!)


/-- Normalize an application if the head is `+`, `*`, `-` or `/`. -/
private def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId):
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
    reduceAux type inst [lhs, rhs] lambdas args #[inst] 6 2
      (lambdaBody? 3 >=> app6? n >=> fun (inst, l, r) =>
        -- check for the form `fun a b x => a x + b x`
        if (l == .app (.bvar 2) (.bvar 0) && r == .app (.bvar 1) (.bvar 0)) then inst else none)
      (fun
        | type, [lhs, rhs] => #[type, type, none, none, lhs, rhs]
        | _, _ => unreachable!)

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
def reducePi (e : Expr) (lambdas : List FVarId) :
    MetaM (Option (Name × List (Array (Option Expr) × List FVarId))) := do
  if let .const n _ := e.getAppFn then
    match n with
    | ``Neg.neg
    | ``Inv.inv     => Option.map (n, ·) <$> reduceUnOp   n e.getAppArgs lambdas
    | ``HVAdd.hVAdd
    | ``HSMul.hSMul => Option.map (n, ·) <$> reduceHActOp n e.getAppArgs lambdas
    | ``HPow.hPow   => Option.map (n, ·) <$> reduceHPow     e.getAppArgs lambdas
    | ``HAdd.hAdd
    | ``HMul.hMul
    | ``HSub.hSub
    | ``HDiv.hDiv   => Option.map (n, ·) <$> reduceHBinOp n e.getAppArgs lambdas
    | _ => return none
  else
    return none

end Lean.Meta.RefinedDiscrTree
