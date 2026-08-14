import Mathlib.Util.CountHeartbeats
import Mathlib.Util.SleepHeartbeats

/-- info: Used approximately 0 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
#count_heartbeats approximately in
example (a : Nat) : a = a := rfl

/-- info: Used approximately 0 heartbeats, which is less than the minimum of 200000. -/
#guard_msgs in
guard_min_heartbeats approximately in
example (a : Nat) : a = a := rfl

/-- info: Used approximately 0 heartbeats, which is less than the minimum of 2000. -/
#guard_msgs in
guard_min_heartbeats approximately 2000 in
example (a : Nat) : a = a := rfl

guard_min_heartbeats approximately 1 in
example (a : Nat) : a = a := rfl

-- The `countHeartbeats` linter and its option-setting `#count_heartbeats` notation were deprecated
-- (lean4, 2026-07-30) in favour of `#count_heartbeats in`, so the linter-specific tests have been
-- retired. This preserves the non-trivial-count coverage via `#count_heartbeats in`, which is
-- exactly what the linter invoked internally for each declaration.
/-- info: Used approximately 1000 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
set_option linter.unusedTactic false in
#count_heartbeats approximately in
example : True := by
  sleep_heartbeats 1000
  trivial
