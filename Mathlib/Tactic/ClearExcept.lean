/-
Copyright (c) 2022 Joshua Clune. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joshua Clune
-/
import Lean

open Lean.Meta

namespace Lean.Elab.Tactic

syntax (name := clearExcept) "clear " "*" " - " (colGt ident)* : tactic

/-- Clears all hypotheses it can besides those provided -/
elab_rules : tactic
  | `(tactic| clear * - $hs:ident*) => do
    let fvarIds ← getFVarIds hs
    liftMetaTactic1 fun goal => do
      let mut toClear : Array FVarId:= #[]
      for decl in ← getLCtx do
        if not (fvarIds.contains decl.fvarId) then
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      tryClearMany goal toClear
