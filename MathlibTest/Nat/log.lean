import Mathlib.Data.Nat.Log

/-!
This used to fail (ran out of heartbeats) but with a new faster `Nat.logC` tagged `csimp`, it
succeeds.
-/

/-- info: 10000000 -/
#guard_msgs in
#eval Nat.log 2 (2 ^ 10000000)
