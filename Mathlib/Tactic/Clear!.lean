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
      for decl in ← getLCtx do
        let hasAnyDependencyFn (fvarId : FVarId) (acc : Bool) : MetaM Bool :=
          return acc || decl.fvarId == fvarId || (← localDeclDependsOn decl fvarId)
        let isDependent ← Array.foldrM hasAnyDependencyFn false fvarIds
        if(isDependent) then
          if let none ← isClass? decl.type then
            toClear := toClear.push decl.fvarId
      tryClearMany goal toClear
