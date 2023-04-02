import Mathlib.Data.ListM
import Mathlib.Lean.CoreM

open Lean

/-- Take an initial segment of a `MetaM` lazy list,
using at most `percent` of the remaining allowed heartbeats. -/
unsafe def ListM.whileAtLeastHeartbeatsPercent
    [Monad m] [MonadLiftT CoreM m] (L : ListM m α) (percent : Nat) : ListM m α :=
ListM.squash do
  let initialHeartbeats ← getRemainingHeartbeats
  pure <| L.takeWhileM fun _ => do
    return .up <| (← getRemainingHeartbeats) * 100 / initialHeartbeats > percent
