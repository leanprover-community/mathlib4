/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Meta.AppBuilder
import Lean.Meta.Basic

/-!
# Additions to `Mathlib/Lean/Meta/Basic.lean`

Likely these already exist somewhere. Pointers welcome.
-/

/--
Restore the metavariable context after execution.
-/
def Lean.Meta.preservingMCtx {α : Type} (x : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  try x finally setMCtx mctx

open Lean Meta

/--
This function is similar to `forallMetaTelescopeReducing`: Given `e` of the
form `forall ..xs, A`, this combinator will create a new metavariable for
each `x` in `xs` until it reaches an `x` whose type is defeq to `t`,
and instantiate `A` with these, while also reducing `A` if needed.
It uses `forallMetaTelescopeReducing`.

This function returns a triple `(mvs, bis, out)` where
- `mvs` is an array containing the new metavariables.
- `bis` is an array containing the binder infos for the `mvs`.
- `out` is `e` but instantiated with the `mvs`.
-/
def Lean.Meta.forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do
      throwError m!"Failed to find {← ppExpr t} as the type of a parameter of {← ppExpr e}."
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

/-- `pureIsDefEq e₁ e₂` is short for `withNewMCtxDepth <| isDefEq e₁ e₂`.
Determines whether two expressions are definitionally equal to each other
when metavariables are not assignable. -/
@[inline]
def Lean.Meta.pureIsDefEq (e₁ e₂ : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq e₁ e₂

/-- `mkRel n lhs rhs` is `mkAppM n #[lhs, rhs]`, but with optimizations for `Eq` and `Iff`. -/
def Lean.Meta.mkRel (n : Name) (lhs rhs : Expr) : MetaM Expr :=
  if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]
