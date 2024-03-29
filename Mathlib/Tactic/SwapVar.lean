/-
Copyright (c) 2022 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/
import Lean.Elab.ElabRules
import Mathlib.Util.Tactic

/-!
# Defines the `swap_var` tactic

Swap the names of two hypotheses.
-/

open Lean Meta Elab.Tactic

namespace Mathlib.Tactic

/-- The parser for swap rules -/
syntax swapRule := ident " ↔"? ppSpace ident

/--
`swap_var swap_rule₁, swap_rule₂, ⋯` applies `swap_rule₁` then `swap_rule₂` then `⋯`.

A *swap_rule* is of the form `x y` or `x ↔ y`, and "applying it" means swapping the variable name
`x` by `y` and vice-versa on all hypotheses and the goal.

```lean
example {P Q : Prop} (q : P) (p : Q) : P ∧ Q := by
  swap_var p ↔ q
  exact ⟨p, q⟩
```
-/
elab "swap_var " swapRules:(colGt swapRule),+ : tactic => do
  let mvarId ← getMainGoal
  let mdecl ← mvarId.getDecl
  let localInstances := mdecl.localInstances
  let lctx ← swapRules.getElems.foldlM (init := mdecl.lctx) fun lctx swapRule ↦ do
    withLCtx lctx localInstances do
      let `(swapRule| $n₁:ident $[↔]? $n₂:ident) := swapRule
        | unreachable!
      let n₁ := n₁.getId
      let n₂ := n₂.getId
      let fvarId₁ := (← getLocalDeclFromUserName n₁).fvarId
      let fvarId₂ := (← getLocalDeclFromUserName n₂).fvarId
      return lctx.setUserName fvarId₁ n₂ |>.setUserName fvarId₂ n₁
  let mdecl := { mdecl with lctx := lctx }
  modifyMCtx fun mctx ↦ { mctx with decls := mctx.decls.insert mvarId mdecl }
