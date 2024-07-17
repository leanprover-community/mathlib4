/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Data.FunLike.Basic
import Mathlib.Tactic.FunProp.ToBatteries


/-!
## `funProp` Meta programming functions like in Lean.Expr.* but for working with bundled morphisms.

Function application in normal lean expression looks like `.app f x` but when we work with bundled
morphism `f` it looks like `.app (.app coe f) x` where `f`. In mathlib `coe` is usually
`DFunLike.coe` but it can be any coercion that is registered with the `coe` attribute.

The main difference when working with expression involving morphisms is that the notion the head of
expression changes. For example in:
```
  coe (f a) b
```
the head of expression is considered to be `f` and not `coe`.
-/

namespace Mathlib
open Lean Meta

namespace Meta.FunProp

namespace Mor

/-- Is `name` a coerction from some function space to functiosn? -/
def isCoeFunName (name : Name) : CoreM Bool := do
  let .some info ← getCoeFnInfo? name | return false
  return info.type == .coeFun

/-- Is `e` a coerction from some function space to functiosn? -/
def isCoeFun (e : Expr) : MetaM Bool := do
  let .some (name,_) := e.getAppFn.const? | return false
  let .some info ← getCoeFnInfo? name | return false
  return e.getAppNumArgs' + 1 == info.numArgs

/-- Morphism application -/
structure App where
  /-- morphism coercion -/
  coe : Expr
  /-- bundled morphism -/
  fn  : Expr
  /-- morphism argument -/
  arg : Expr

/-- Is `e` morphism application? -/
def isMorApp? (e : Expr) : MetaM (Option App) := do

  let .app (.app coe f) x := e | return none
  if ← isCoeFun coe then
    return .some { coe := coe, fn := f, arg := x }
  else
    return none

/--
Weak normal head form of an expression involving morphism applications. Additionally, `pred`
can specify which when to unfold definitions.

For example calling this on `coe (f a) b` will put `f` in weak normal head form instead of `coe`.
 -/
partial def whnfPred (e : Expr) (pred : Expr → MetaM Bool) (cfg : WhnfCoreConfig := {}) :
    MetaM Expr := do
  whnfEasyCases e fun e => do
    let e ← whnfCore e cfg

    if let .some ⟨coe,f,x⟩ ← isMorApp? e then
      let f ← whnfPred f pred cfg
      if cfg.zeta then
        return (coe.app f).app x
      else
        return ← letTelescope f fun xs f' =>
          mkLambdaFVars xs ((coe.app f').app x)

    if (← pred e) then
        match (← unfoldDefinition? e) with
        | some e => whnfPred e pred cfg
        | none   => return e
    else
      return e

/--
Weak normal head form of an expression involving morphism applications.

For example calling this on `coe (f a) b` will put `f` in weak normal head form instead of `coe`.
 -/
def whnf (e : Expr)  (cfg : WhnfCoreConfig := {}) : MetaM Expr :=
  whnfPred e (fun _ => return false) cfg


/-- Argument of morphism application that stores corresponding coercion if necessary -/
structure Arg where
  /-- argument of type `α` -/
  expr : Expr
  /-- coercion `F → α → β` -/
  coe : Option Expr := none
  deriving Inhabited

/-- Morphism application -/
def app (f : Expr) (arg : Arg) : Expr :=
  match arg.coe with
  | .none => f.app arg.expr
  | .some coe => (coe.app f).app arg.expr


/-- Given `e = f a₁ a₂ ... aₙ`, returns `k f #[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
partial def withApp {α} (e : Expr) (k : Expr → Array Arg → MetaM α) : MetaM α :=
  go e #[]
where
  /-- -/
  go : Expr → Array Arg →  MetaM α
    | .mdata _ b, as => go b as
    | .app (.app c f) x, as => do
      if ← isCoeFun c then
        go f (as.push { coe := c, expr := x})
      else
        go (.app c f) (as.push { expr := x})
    | .app f a, as =>
      go f (as.push { expr := a })
    | f        , as => k f as.reverse


/--
If the given expression is a sequence of morphism applications `f a₁ .. aₙ`, return `f`.
Otherwise return the input expression.
-/
def getAppFn (e : Expr) : MetaM Expr :=
  match e with
  | .mdata _ b => getAppFn b
  | .app (.app c f) _ => do
    if ← isCoeFun c then
      getAppFn f
    else
      getAppFn (.app c f)
  | .app f _ =>
    getAppFn f
  | e => return e

/-- Given `f a₁ a₂ ... aₙ`, returns `#[a₁, ..., aₙ]` where `f` can be bundled morphism. -/
def getAppArgs (e : Expr) : MetaM (Array Arg) := withApp e fun _ xs => return xs

/-- `mkAppN f #[a₀, ..., aₙ]` ==> `f a₀ a₁ .. aₙ` where `f` can be bundled morphism. -/
def mkAppN (f : Expr) (xs : Array Arg) : Expr :=
  xs.foldl (init := f) (fun f x =>
    match x with
    | ⟨x, .none⟩ => (f.app x)
    | ⟨x, .some coe⟩ => (coe.app f).app x)
