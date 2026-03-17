/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean
public import Mathlib.CategoryTheory.Monoidal.Category

open Lean Meta Elab Tactic CategoryTheory

elab "kernel_instance" : tactic => do
  evalTactic (← `(tactic| try dsimp only [MonoidalCategory.tensorUnit,
    MonoidalCategory.tensorObj]))
  let goal ← getMainGoal
  let goalType ← goal.getType
  let result ← synthInstance? goalType
  match result with
  | some inst =>
    goal.assign inst
  | none =>
    let lctx ← getLCtx
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let declName := decl.userName
      evalTactic (← `(tactic| try have := $(mkIdent declName).2))
    evalTactic (← `(tactic| try infer_instance))
    try
      let _ ← getMainGoal
    catch _ =>
      return ()
    throwError "kernel_instance tactic failed."

elab "kernel_cat" : tactic => do
  evalTactic (← `(tactic| try rw [Subtype.ext_iff]))
  evalTactic (← `(tactic| try simp only))
  evalTactic (← `(tactic| dsimp only [CategoryStruct.id, CategoryStruct.comp,
    MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
    MonoidalCategory.tensorHom, MonoidalCategory.tensorUnit, MonoidalCategory.tensorObj,
    MonoidalCategory.associator, MonoidalCategory.leftUnitor, MonoidalCategory.rightUnitor]))
