/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Lean.Data.Format

/-!
# `Ineq` datatype

This file contains an enum `Ineq` (whose options are `eq`, `le`, `lt`), and operations involving it.
The type `Ineq` is one of the fundamental objects manipulated by the `linarith` tactic (and, in
future, also the `linear_combination` tactic).
-/

open Lean

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

end Linarith
