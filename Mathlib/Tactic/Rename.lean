/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import Lean

namespace Mathlib.Tactic

open Lean Elab.Tactic Meta

syntax renameArg := term " => " ident

/-- `rename' h => hnew` renames the hypothesis named `h` to `hnew`. -/
syntax (name := rename') "rename'" (ppSpace renameArg),* : tactic

elab_rules : tactic
  | `(tactic| rename' $[$as:term => $bs:ident],*) =>
    for a in as, b in bs do
      withMainContext do
        let fvarId ← getFVarId a
        let lctxNew := (← getLCtx).setUserName fvarId b.getId
        let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances)
          (← getMainTarget) MetavarKind.syntheticOpaque (← getMainTag)
        assignExprMVar (← getMainGoal) mvarNew
        replaceMainGoal [mvarNew.mvarId!]
