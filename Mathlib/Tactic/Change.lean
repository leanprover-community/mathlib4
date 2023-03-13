/-
Copyright (c) 2023 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Lean

/-!
# The `change` tactic

This file provides an implementation of the `change` tactic, whose syntax is declared in
the Lean 4 core.

-/

open Lean Elab Tactic Meta

elab_rules : tactic
  | `(tactic| change $newType:term $[$loc:location]?) => do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := fun h ↦ do
        let hTy ← h.getType
        let (e, gs) ← elabTermWithHoles newType none (← getMainTag) (allowNaturalHoles := true)
        liftMetaTactic fun mvarId ↦ do
          unless ← withAssignableSyntheticOpaque (isDefEq e hTy) do
            let h' ← h.getUserName
            throwTacticEx `change mvarId
              m!"given type{indentExpr e}\nis not definitionally equal at {h'} to{indentExpr hTy}"
          return (← mvarId.changeLocalDecl h e) :: gs)
      (atTarget := do
        let tgt ← getMainTarget
        let (e, gs) ← elabTermWithHoles newType none (← getMainTag) (allowNaturalHoles := true)
        liftMetaTactic fun mvarId ↦ do
          unless ← withAssignableSyntheticOpaque (isDefEq e tgt) do
            throwTacticEx `change mvarId
              m!"given type{indentExpr e}\nis not definitionally equal to{indentExpr tgt}"
          return (← mvarId.change e) :: gs)
      (failed := fun _ ↦ throwError "change tactic failed")
