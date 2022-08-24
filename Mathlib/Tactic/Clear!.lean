/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

/-- A variant of `clear` which clears not only the given hypotheses but also any other hypotheses
    depending on them -/
syntax (name := clear!) "clear!" (ppSpace colGt ident)* : tactic

elab_rules : tactic
  | `(tactic| clear! $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal => do
      let mut toClear : Array FVarId := #[]
      let lctx ← getLCtx
      for fvar in fvarIds do
        let deps := (← collectForwardDeps #[mkFVar fvar] true).map (·.fvarId!)
        if ← deps.allM fun dep => return (← isClass? (lctx.get! dep).type).isNone then
          toClear := toClear ++ deps
      goal.tryClearMany toClear
