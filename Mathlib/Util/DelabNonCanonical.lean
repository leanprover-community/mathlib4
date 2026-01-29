/-
Copyright (c) 2025 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Init
public meta import Lean.PrettyPrinter.Delaborator.Builtins

/-! Delab checking canonicity.

Provides a series of monadic functions in `DelabM` for delaborating expressions differently
if their given instances differ (by definitional equality) with what is synthesized.
Synthesized instances are considered 'canonical' for this purpose.
-/

public meta section
open Lean Meta PrettyPrinter.Delaborator SubExpr

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
  withReducibleAndInstances <| return (← Meta.isDefEq inst synthInst, instD)

/-- Delaborate an expression with arity `arity` into a unary notation `mkStx` iff the argument
`arg` is a non-canonical instance (is not defeq to what is synthesized for its type, or else
instance synthesis fails). -/
def delabUnary (arity arg : Nat) (mkStx : Term → DelabM Term) : Delab :=
  withOverApp arity <| whenPPOption Lean.getPPNotation do
    let (false, instD) ← withNaryArg arg delabCheckingCanonical | failure
    mkStx instD

/-- Delaborate an expression with arity `arity` into a binary notation `mkStx` iff either
argument `arg₁` or `arg₂` are non-canonical instance (are not defeq to what is synthesized for
its type, or else instance synthesis fails). -/
def delabBinary (arity arg₁ arg₂ : Nat) (mkStx : Term → Term → DelabM Term) : Delab :=
  withOverApp arity <| whenPPOption Lean.getPPNotation do
    let (canonα?, instDα) ← withNaryArg arg₁ delabCheckingCanonical
    let (canonβ?, instDβ) ← withNaryArg arg₂ delabCheckingCanonical
    -- fall through to normal delab if both canonical
    if canonα? && canonβ? then failure
    mkStx instDα instDβ
