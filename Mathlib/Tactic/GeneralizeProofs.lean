/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

/--
Generalize proofs in the goal, naming them with the provided list.

For example:
```lean
example : list.nth_le [1, 2] 1 dec_trivial = 2 := by
  -- ⊢ [1, 2].nth_le 1 _ = 2
  generalize_proofs h,
  -- h : 1 < [1, 2].length
  -- ⊢ [1, 2].nth_le 1 h = 2
```-/
syntax (name := generalizeProofs) "generalize_proofs" (ppSpace colGt ident)* : tactic

elab_rules : tactic
  | `(tactic| generalize_proofs $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal => do
      let mut toClear : Array FVarId := #[]
      for decl in ← getLCtx do
        unless fvarIds.contains decl.fvarId do
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      goal.tryClearMany toClear
