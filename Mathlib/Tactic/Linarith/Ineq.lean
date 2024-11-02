/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Lean.Expr.Basic

/-!
# `Ineq` datatype

This file contains an enum `Ineq` (whose options are `eq`, `le`, `lt`), and operations involving it.
The type `Ineq` is one of the fundamental objects manipulated by the `linarith` tactic (and, in
future, also the `linear_combination` tactic).
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

/--
`getRelSides e` returns the left and right hand sides of `e` if `e` is a comparison,
and fails otherwise.
This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
 -/
def getRelSides (e : Expr) : MetaM (Expr × Expr) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return (a, b)
  | (``LE.le, #[_, _, a, b]) => return (a, b)
  | (``Eq, #[_, a, b]) => return (a, b)
  | (``GE.ge, #[_, _, a, b]) => return (a, b)
  | (``GT.gt, #[_, _, a, b]) => return (a, b)
  | _ => throwError "Not a comparison (getRelSides) : {e}"

/-- If `prf` is a proof of `t R s`, `leftOfIneqProof prf` returns `t`. -/
def leftOfIneqProof (prf : Expr) : MetaM Expr := do
  let (t, _) ← getRelSides (← inferType prf)
  return t

/-- If `prf` is a proof of `t R s`, `typeOfIneqProof prf` returns the type of `t`. -/
def typeOfIneqProof (prf : Expr) : MetaM Expr := do
  inferType (← leftOfIneqProof prf)

/--
`parseCompAndExpr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
If it is, it returns the comparison along with `t`.
-/
def parseCompAndExpr (e : Expr) : MetaM (Ineq × Expr) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``LT.lt, #[_, _, e, z]) => if z.zero? then return (Ineq.lt, e) else throwNotZero z
  | (``LE.le, #[_, _, e, z]) => if z.zero? then return (Ineq.le, e) else throwNotZero z
  | (``Eq, #[_, e, z]) => if z.zero? then return (Ineq.eq, e) else throwNotZero z
  | _ => throwError "invalid comparison: {e}"
  where /-- helper function for error message -/
  throwNotZero (z : Expr) := throwError "invalid comparison, rhs not zero: {z}"

end Linarith
