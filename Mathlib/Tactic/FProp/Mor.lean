/-
Copyright (c) 2024 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan
-/
import Lean
import Mathlib.Data.FunLike.Basic


/-!
## `fprop` meta programming function like in Lean.Expr.* but for working with bundled morphisms

Function application in normal lean expression looks like `.app f x` but when we work with bundled
morphism `f` it looks like `.app (.app coe f) x` where `f`. In mathlib the convention is that `coe`
is aplication of `DFunLike.coe` and this is assumed through out this file. It does not work with
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

namespace Meta.FProp

namespace Mor

/-- Argument of morphism aplication that stores corresponding coercion if necessary -/
structure Arg where
  expr : Expr -- argument of type `α`
  coe : Option Expr -- coercion `F → α → β`
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

An example when coersions are involved:
`(fun x => ⇑((fun y => e) a)) b` ==> `e[y/a, x/b]`. -/
def headBeta (e : Expr) : Expr :=
  Mor.withApp e fun f xs =>
    xs.foldl (init := f) fun e x =>
      match x.coe with
      | none => e.beta #[x.expr]
      | .some c => (c.app e).app x.expr

end Mor
