import Mathlib.Tactic.Ring

set_option linter.style.header false

/-- info: Used 7 heartbeats, which is less than the current maximum of 200000. -/
#guard_msgs in
count_heartbeats in
example (a : Nat) : a = a := rfl

/-- info: Used 7 heartbeats, which is less than the minimum of 200000. -/
#guard_msgs in
guard_min_heartbeats in
example (a : Nat) : a = a := rfl

/-- info: Used 7 heartbeats, which is less than the minimum of 2000. -/
#guard_msgs in
guard_min_heartbeats 2000 in
example (a : Nat) : a = a := rfl

guard_min_heartbeats 1 in
example (a : Nat) : a = a := rfl
