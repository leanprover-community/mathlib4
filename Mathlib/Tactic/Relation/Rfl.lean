/-
Copyright (c) 2022 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen
-/
import Lean.Meta.Tactic.Rfl

/-!
# `Lean.MVarId.liftReflToEq`

Convert a goal of the form `x ~ y` into the form `x = y`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute `[refl]`.
If this can't be done, returns the original `MVarId`.
-/

namespace Mathlib.Tactic

open Lean Meta Elab Tactic Rfl

/--
This tactic applies to a goal whose target has the form `x ~ x`, where `~` is a reflexive
relation, that is, a relation which has a reflexive lemma tagged with the attribute [refl].
-/
def rflTac : TacticM Unit :=
  withMainContext do liftMetaFinishingTactic (·.applyRfl)

/-- If `e` is the form `@R .. x y`, where `R` is a reflexive
relation, return `some (R, x, y)`.
As a special case, if `e` is `@HEq α a β b`, return ``some (`HEq, a, b)``. -/
def _root_.Lean.Expr.relSidesIfRefl? (e : Expr) : MetaM (Option (Name × Expr × Expr)) := do
  if let some (_, lhs, rhs) := e.eq? then
    return (``Eq, lhs, rhs)
  if let some (lhs, rhs) := e.iff? then
    return (``Iff, lhs, rhs)
  if let some (_, lhs, _, rhs) := e.heq? then
    return (``HEq, lhs, rhs)
  if let .app (.app rel lhs) rhs := e then
    unless (← (reflExt.getState (← getEnv)).getMatch rel reflExt.config).isEmpty do
      match rel.getAppFn.constName? with
      | some n => return some (n, lhs, rhs)
      | none => return none
  return none
