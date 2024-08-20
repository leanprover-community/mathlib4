/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
import Mathlib.Init
import Lean.Elab.Tactic.ElabTerm

/-!
# The `clear*` tactic

This file provides a variant of the `clear` tactic, which clears all hypotheses it can
besides a provided list.
-/

open Lean.Meta

namespace Lean.Elab.Tactic

/-- Clears all hypotheses it can, except those provided after a minus sign. Example:
```
  clear * - h₁ h₂
```
-/
syntax (name := clearExcept) "clear " "*" " -" (ppSpace colGt ident)* : tactic

elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal ↦ do
      let mut toClear : Array FVarId := #[]
      for decl in ← getLCtx do
        unless fvarIds.contains decl.fvarId do
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      goal.tryClearMany toClear

end Lean.Elab.Tactic
