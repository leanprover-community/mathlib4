/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM

/-!
# Additional functions using `CoreM` state.
-/

open Lean

/-- Return the current `maxHeartbeats`. -/
def getMaxHeartbeats : CoreM Nat := do pure (← read).maxHeartbeats

/-- Return the remaining heartbeats available in this computation. -/
def getRemainingHeartbeats : CoreM Nat := do pure <| (← getMaxHeartbeats) - (← IO.getNumHeartbeats)

/--
Return the percentage of the max heartbeats allowed
that have been consumed so far in this computation.
-/
def heartbeatsPercent : CoreM Nat := do pure <| (← IO.getNumHeartbeats) * 100 / (← getMaxHeartbeats)

/-- Log a message if it looks like we ran out of time. -/
def reportOutOfHeartbeats (tac : Name) (stx : Syntax) : CoreM Unit := do
  if (← heartbeatsPercent) ≥ 90 then
    logInfoAt stx (s!"`{tac}` stopped because it was running out of time.\n" ++
      "You may get better results using `set_option maxHeartbeats 0`.")
