/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Lean
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Kernel category tactics

Auxiliary tactics for proofs in kernel-based categories.

## Main declarations

* `kernel_instance`: tries to synthesize kernel instances by exposing subtype fields in context.
* `kernel_cat`: reduces categorical equalities to equalities of kernels.
-/

open Lean Meta Elab Tactic CategoryTheory

/-- `kernel_instance` tries to close instance goals by progressively exposing `property` fields
of subtypes in the local context, then calling typeclass inference. -/
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

/-- `kernel_cat` turns a categorical equation into an equation on the underlying kernels. -/
elab "kernel_cat" : tactic => do
  evalTactic (← `(tactic| try rw [Subtype.ext_iff]))
  evalTactic (← `(tactic| try simp only))
  evalTactic (← `(tactic| dsimp only [CategoryStruct.id, CategoryStruct.comp,
    MonoidalCategory.whiskerLeft, MonoidalCategory.whiskerRight,
    MonoidalCategory.tensorHom, MonoidalCategory.tensorUnit, MonoidalCategory.tensorObj,
    MonoidalCategory.associator, MonoidalCategory.leftUnitor, MonoidalCategory.rightUnitor]))
