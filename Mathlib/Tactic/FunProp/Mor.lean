/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Data.FunLike.Basic

import Mathlib.Tactic.FunProp.ToStd


/-!
## `funProp` meta programming function like in Lean.Expr.* but for working with bundled morphisms

Function application in normal lean expression looks like `.app f x` but when we work with bundled
morphism `f` it looks like `.app (.app coe f) x` where `f`. In mathlib the convention is that `coe`
is application of `DFunLike.coe` and this is assumed through out this file. It does not work with
Lean's `CoeFun.coe`.

The main difference when working with expression involving morphisms is that the notion the head of
expression changes. For example in:
```
  coe (f a) b = ⇑(f a) b
```
the head of expression is considered to be `f` and not `coe`.
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

namespace Mor

/-- Argument of morphism application that stores corresponding coercion if necessary -/
structure Arg where
  /-- argument of type `α` -/
  expr : Expr
  /-- coercion `F → α → β` -/
  coe : Option Expr
  deriving Inhabited

/-- Morphism application -/
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | .none => f.app arg.expr
  | .some coe => (coe.app f).app arg.expr

/-- Counts the number `n` of arguments for an expression `f a₁ .. aₙ` where `f` can be bundled
morphism. -/
partial def getAppNumArgs (e : Expr) :=
  go e 0
where
  /-- -/
  go : Expr → Nat → Nat
    | .mdata _ b, n => go b n
    | .app f _  , n =>
      if f.isAppOfArity' ``DFunLike.coe 5 then
        go f.appArg! (n + 1)
      else
        go f (n + 1)
    | _        , n => n

/-- Given `e = f a₁ a₂ ... aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
def withApp {α} (e : Expr) (k : Expr → Array Arg → α) : α :=
  let nargs := getAppNumArgs e
  go e (mkArray nargs default) (nargs - 1)
where
  /-- -/
  go : Expr → Array Arg → Nat → α
    | .mdata _ b, as, i => go b as i
    | .app (.app c f) a  , as, i =>
      if c.isAppOfArity' ``DFunLike.coe 4 then
        go f (as.set! i ⟨a,.some c⟩) (i-1)
      else
        go (.app c f) (as.set! i ⟨a,.none⟩) (i-1)
    | .app f a  , as, i =>
      go f (as.set! i ⟨a,.none⟩) (i-1)
    | f        , as, _ => k f as

/--
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, return `f`.
Otherwise return the input expression.
-/
def getAppFn (e : Expr) : Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ =>
    if c.isAppOfArity' ``DFunLike.coe 4 then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => e

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
def getAppArgs (e : Expr) : Array Arg := withApp e fun _ xs => xs


/-- `mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism. -/
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, .some coe⟩ => (coe.app f).app x)

private partial def getTypeArityAux (type : Expr) (n:Nat) : MetaM Nat := do
  forallTelescopeReducing type fun xs b => do
    try
      let c ← mkAppOptM ``DFunLike.coe #[b,none,none,none]
      return ← getTypeArityAux (← inferType c) (xs.size-1 + n)
    catch _ =>
      return xs.size + n

/-- Get arity of morphism `f`. To get maximal arity of morphism `f`, this function tries to
synthesize instance of `FunLike` as many times as possible.
-/
def getArity (f : Expr) : MetaM Nat := do
  getTypeArityAux (← inferType f) 0

/-- Arity of declared morphism with name `decl`. -/
def constArity (decl : Name) : MetaM Nat := do
  let info ← getConstInfo decl
  return ← getTypeArityAux info.type 0

/-- `(fun x => e) a` ==> `e[x/a]`

An example when coercions are involved:
`(fun x => ⇑((fun y => e) a)) b` ==> `e[y/a, x/b]`. -/
def headBeta (e : Expr) : Expr :=
  Mor.withApp e fun f xs =>
    xs.foldl (init := f) fun e x =>
      match x.coe with
      | none => e.beta #[x.expr]
      | .some c => (c.app e).app x.expr

end Mor



/--
Split morphism function into composition by specifying over which arguments in the lambda body this
split should be done.
 -/
def splitMorToCompOverArgs (e : Expr) (argIds : Array Nat) : MetaM (Option (Expr × Expr)) := do
  let e ←
    if e.isLambda
    then pure e
    else do
      let X := (← inferType e).bindingDomain!
      pure (.lam `x X (.app e (.bvar 0)) default)

  match e with
  | .lam name _ _ _ =>
    lambdaTelescope e λ xs b => do
      let x := xs[0]!

      let fn := Mor.getAppFn b
      let mut args := Mor.getAppArgs b

      let mut lctx ← getLCtx
      let instances ← getLocalInstances

      let mut yVals : Array Expr := #[]
      let mut yVars : Array Expr := #[]

      let xIds := xs.map fun x => x.fvarId!
      let xIds' := xIds[1:].toArray

      for argId in argIds do
        let yVal := args[argId]!

        -- abstract over trailing arguments
        let xs'' := xIds'.filterMap
          (fun xId => if yVal.expr.containsFVar xId then .some (Expr.fvar xId) else .none)
        let yVal' ← mkLambdaFVars xs'' yVal.expr
        let yId ← withLCtx lctx instances mkFreshFVarId
        lctx := lctx.mkLocalDecl yId (name.appendAfter (toString argId)) (← inferType yVal')
        let yVar := Expr.fvar yId
        yVars := yVars.push yVar
        yVals := yVals.push yVal'
        args := args.set! argId ⟨Lean.mkAppN yVar xs'', yVal.coe⟩

      let g  ← mkLambdaFVars #[x] (← mkProdElem yVals)
      let f ← withLCtx lctx instances do
        (mkLambdaFVars (yVars ++ xs[1:]) (Mor.mkAppN fn args))
        >>=
        mkUncurryFun yVars.size

      -- `f` should not contain `x`
      -- if they do then the split is unsuccessful
      if f.containsFVar xIds[0]! then
        return none

      return (f, g)

  | _ => return none


/--
Split morphism function into composition by specifying over which arguments in the lambda body this
split should be done.
 -/
def splitMorToComp (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e with
  | .lam .. =>
    lambdaTelescope e λ xs b => do
      let xId := xs[0]!.fvarId!

      Mor.withApp b fun _ xs =>
        let argIds := xs
          |>.mapIdx (fun i x => if x.expr.containsFVar xId then .some i.1 else none)
          |>.filterMap id
        splitMorToCompOverArgs e argIds

  | _ =>
   splitMorToCompOverArgs e #[Mor.getAppNumArgs e]
