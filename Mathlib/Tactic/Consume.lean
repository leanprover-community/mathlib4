/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Lean
import Mathlib.Tactic.InferParam

/-!
# Consume

Introduces a tactic `consume` that consumes type annotations of the form `autoParam` and `optParam`.

Also add a macro that makes constructor behave more like the `where ...` syntax, attempting
to infer the argument from optional or auto parameters, and if this fails consumes the annotations.

-/

open Lean Elab Tactic
elab "consume" : tactic => do
  withMainContext do
    let mvarIds ← getMainGoal
    mvarIds.setType (← mvarIds.getType).consumeTypeAnnotations

macro "constructor" : tactic =>
  `(tactic| constructor <;> ((try infer_param) <;> consume))
