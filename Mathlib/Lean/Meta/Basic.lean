/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.Meta.Basic
import Lean.Meta.AppBuilder

/-!
# Additions to `Lean.Meta.Basic`

Likely these already exist somewhere. Pointers welcome.
-/

set_option autoImplicit true

/--
Restore the metavariable context after execution.
-/
def Lean.Meta.preservingMCtx (x : MetaM α) : MetaM α := do
  let mctx ← getMCtx
  try x finally setMCtx mctx

/-- Determines whether two expressions are definitionally equal to each other without any mvar
    assignments. -/
@[inline]
def Lean.Meta.pureIsDefEq (e₁ e₂ : Expr) : MetaM Bool :=
  withNewMCtxDepth <| isDefEq e₁ e₂

/-- Similar to `mkAppM n #[lhs, rhs]`, but handles `Eq` and `Iff` more efficiently. -/
def Lean.Meta.mkRel (n : Name) (lhs rhs : Expr) : MetaM Expr :=
  if n == ``Eq then
    mkEq lhs rhs
  else if n == ``Iff then
    return mkApp2 (.const ``Iff []) lhs rhs
  else
    mkAppM n #[lhs, rhs]
