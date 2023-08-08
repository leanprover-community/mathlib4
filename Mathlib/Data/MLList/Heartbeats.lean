/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Std.Data.MLList.Basic
import Mathlib.Lean.CoreM

/-!
# Truncate a `MLList` when running out of available heartbeats.
-/

open Lean.Core (CoreM)

/-- Take an initial segment of a `MetaM` lazy list,
trying to leave at least `percent` of the remaining allowed heartbeats. -/
def MLList.whileAtLeastHeartbeatsPercent [Monad m] [MonadLiftT CoreM m]
    (L : MLList m α) (percent : Nat := 10) : MLList m α :=
MLList.squash fun _ => do
  if (← getMaxHeartbeats) = 0 then do
    return L
  let initialHeartbeats ← getRemainingHeartbeats
  pure <| L.takeWhileM fun _ => do
    return .up <| (← getRemainingHeartbeats) * 100 / initialHeartbeats > percent
