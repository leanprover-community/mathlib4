/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Data.Ineq
public meta import Mathlib.Lean.Expr.Basic

/-!
# Parsing inequalities in expressions

This file provides expression recognizers returning the `Mathlib.Ineq` comparison type.
-/

@[expose] public meta section

open Lean Meta

namespace Lean.Expr
open Mathlib

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, and return this relation (as a
`Mathlib.Ineq`) together with the type in which the (in)equality occurs and the two sides of the
(in)equality.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def ineq? (e : Expr) : MetaM (Ineq × Expr × Expr × Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, or the negation of such, and return this
relation (as a `Mathlib.Ineq`) together with the type in which the (in)equality occurs, the two
sides of the (in)equality, and a Boolean flag indicating the presence or absence of the `¬`.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def ineqOrNotIneq? (e : Expr) : MetaM (Bool × Ineq × Expr × Expr × Expr) := do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)

end Lean.Expr
