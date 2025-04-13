/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Init
import Lean.Meta.Tactic.Symm

/-!
# `relSidesIfSymm?`
-/

open Lean Meta Symm

namespace Mathlib.Tactic

open Lean.Elab.Tactic

/-- If `e` is the form `@R .. x y`, where `R` is a symmetric
relation, return `some (R, x, y)`.
As a special case, if `e` is `@HEq α a β b`, return ``some (`HEq, a, b)``. -/
def _root_.Lean.Expr.relSidesIfSymm? (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (symmExt.getState (← getEnv)).getMatch rel).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none

end Mathlib.Tactic
