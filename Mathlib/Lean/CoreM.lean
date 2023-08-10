/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean
import Mathlib.Tactic.ToExpr

/-!
# Additional functions using `CoreM` state.
-/

open Lean Core

/-- Return the current `maxHeartbeats`. -/
def getMaxHeartbeats : CoreM Nat := do pure <| (← read).maxHeartbeats

/-- Return the current `initHeartbeats`. -/
def getInitHeartbeats : CoreM Nat := do pure <| (← read).initHeartbeats

/-- Return the remaining heartbeats available in this computation. -/
def getRemainingHeartbeats : CoreM Nat := do
  pure <| (← getMaxHeartbeats) - ((← IO.getNumHeartbeats) - (← getInitHeartbeats))

/--
Return the percentage of the max heartbeats allowed
that have been consumed so far in this computation.
-/
def heartbeatsPercent : CoreM Nat := do
  pure <| ((← IO.getNumHeartbeats) - (← getInitHeartbeats)) * 100 / (← getMaxHeartbeats)

/-- Log a message if it looks like we ran out of time. -/
def reportOutOfHeartbeats (tac : Name) (stx : Syntax) (threshold : Nat := 90) : CoreM Unit := do
  if (← heartbeatsPercent) ≥ threshold then
    logInfoAt stx (s!"`{tac}` stopped because it was running out of time.\n" ++
      "You may get better results using `set_option maxHeartbeats 0`.")

/--
Term elaborator that retrieves the current `SearchPath`.
-/
elab "compileTimeSearchPath" : term =>
  return toExpr (← searchPathRef.get)

/--
Run a `CoreM α` in a fresh `Environment` with specified `modules : List Name` imported.
-/
def CoreM.withImportModules (modules : List Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 1024) (fileName := "") :
    IO α := unsafe do
  searchPathRef.set (searchPath.getD compileTimeSearchPath)
  Lean.withImportModules (modules.map (Import.mk · false)) options trustLevel fun env =>
    let ctx := {fileName, options, fileMap := default}
    let state := {env}
    Prod.fst <$> (CoreM.toIO · ctx state) do
      run
