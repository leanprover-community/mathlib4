/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Lean.Expr.Basic

/-!
# `Ineq` datatype

This file contains an enum `Ineq` (whose constructors are `eq`, `le`, `lt`), and operations
involving it. The type `Ineq` is one of the fundamental objects manipulated by the `linarith` tactic
(and, in future, also the `linear_combination` tactic).
-/

open Lean Elab Tactic Meta

namespace Linarith

/-! ### Inequalities -/

/-- The three-element type `Ineq` is used to represent the strength of a comparison between
terms. -/
inductive Ineq : Type
  | eq | le | lt
deriving DecidableEq, Inhabited, Repr

namespace Ineq

/--
`max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : Ineq → Ineq → Ineq
  | lt, _ => lt
  | _, lt => lt
  | le, _ => le
  | _, le => le
  | eq, eq => eq

/-- `Ineq` is ordered `eq < le < lt`. -/
def cmp : Ineq → Ineq → Ordering
  | eq, eq => Ordering.eq
  | eq, _ => Ordering.lt
  | le, le => Ordering.eq
  | le, lt => Ordering.lt
  | lt, lt => Ordering.eq
  | _, _ => Ordering.gt

/-- Prints an `Ineq` as the corresponding infix symbol. -/
def toString : Ineq → String
  | eq => "="
  | le => "≤"
  | lt => "<"

instance : ToString Ineq := ⟨toString⟩

instance : ToFormat Ineq := ⟨fun i => Ineq.toString i⟩

end Ineq

/-! ### Parsing inequalities -/

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, and return this relation (as a
`Linarith.Ineq`) together with the type in which the (in)equality occurs and the two sides of the
(in)equality.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def _root_.Lean.Expr.ineq? (e : Expr) : MetaM (Ineq × Expr × Expr × Expr) := do
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

/-- If `prf` is a proof of `t R s`, `leftOfIneqProof prf` returns `t`. -/
def leftOfIneqProof (prf : Expr) : MetaM Expr := do
  let e ← inferType prf
  let (_, _, t, _) ← e.ineq?
  return t

/-- If `prf` is a proof of `t R s`, `typeOfIneqProof prf` returns the type of `t`. -/
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  let e ← inferType prf
  let (_, ty, _) ← e.ineq?
  return ty

/--
`parseCompAndExpr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
If it is, it returns the comparison along with `t`.
-/
def parseCompAndExpr (e : Expr) : MetaM (Ineq × Expr) := do
  let (rel, _, e, z) ← e.ineq?
  if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"

end Linarith
