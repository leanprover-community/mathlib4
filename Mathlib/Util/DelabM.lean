/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-! Delab helpers

Provides monadic functions in `DelabM` that can be factored out of their original application.
-/

public meta section

/-- When the delab reader is pointed at an expression for an instance, returns `(true, t)`
**iff** instance synthesis succeeds and produces a defeq instance; otherwise returns `(false, t)`.
-/
def delabCheckingCanonical : DelabM (Bool × Term) := do
  let instD ← delab
  let inst ← getExpr
  let type ← inferType inst
  -- if there is no synthesized instance, still return `false`
  -- (because `inst` is still non-canonical)
  let .some synthInst ← Meta.trySynthInstance type | return (false, instD)
  return (← Meta.isDefEq inst synthInst, instD)
