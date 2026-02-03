/-
Copyright (c) 2026 Pavel Grigorenko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Grigorenko
-/
module

public import Mathlib.Init
meta import Lean.Elab.Tactic.Basic

/-! # `clear_unneeded` tactic -/

meta section

namespace Mathlib.Tactic.ClearUnneeded
open Lean Meta Elab.Tactic

private def isNonempty (e : Expr) : MetaM Bool := do
  let lvl ← Meta.getLevel e
  let nonempty := Expr.app (.const ``Nonempty [lvl]) e
  let inst ← trySynthInstance nonempty
  return inst.toOption.isSome

private def isUnneeded (decl : LocalDecl) : MetaM Bool := do
  if ← decl.fvarId.hasForwardDeps then
    return false
  if ← isNonempty decl.type then
    return true
  return false

/--
Removes hypotheses that don't appear elsewhere in the goal
and whose types satisfy `Nonempty`, which are therefore unneeded.
-/
elab "clear_unneeded" : tactic =>
  liftMetaTactic1 fun goal ↦ do
    let mut toClear := #[]
    for decl in ← getLCtx do
      if ← isUnneeded decl then
        toClear := toClear.push decl.fvarId
    goal.tryClearMany toClear

end Mathlib.Tactic.ClearUnneeded
