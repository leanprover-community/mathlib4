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
