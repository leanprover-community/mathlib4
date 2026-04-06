/-
Copyright (c) 2026 Onyeka Obi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Onyeka Obi
-/
module

public import Mathlib.Init
meta import Lean.Elab.Tactic.Basic

/-!
# The `clear_unneeded` tactic

This file provides `clear_unneeded`, a tactic that removes hypotheses whose types are `Nonempty`
and that have no forward dependencies in the local context. Such hypotheses carry no information
beyond the existence of a term of that type, which is already witnessed by the `Nonempty` instance.
-/

meta section

namespace Mathlib.Tactic.ClearUnneeded
open Lean Meta Elab.Tactic

/-- Returns `true` when `e` has a `Nonempty` instance. -/
private def hasNonemptyInst (e : Expr) : MetaM Bool := do
  let lvl ← Meta.getLevel e
  let nonempty := Expr.app (.const ``Nonempty [lvl]) e
  return (← trySynthInstance nonempty).toOption.isSome

/--
`clear_unneeded` removes hypotheses that are not depended upon by any later hypothesis and whose
types satisfy `Nonempty`. Because a `Nonempty` instance already witnesses the existence of a term
of that type, retaining a specific witness is unnecessary when nothing else in the context refers
to it.

```lean
example [Nonempty α] (a : α) (b : β) : α := by
  -- `a` is cleared (α is Nonempty and nothing depends on a)
  -- `b` is kept (β has no Nonempty instance)
  clear_unneeded
  exact Classical.choice ‹_›
```
-/
elab "clear_unneeded" : tactic =>
  liftMetaTactic1 fun goal => do
    let mut toClear := #[]
    for decl in ← getLCtx do
      if !(← decl.fvarId.hasForwardDeps) && (← hasNonemptyInst decl.type) then
        toClear := toClear.push decl.fvarId
    goal.tryClearMany toClear

end Mathlib.Tactic.ClearUnneeded
