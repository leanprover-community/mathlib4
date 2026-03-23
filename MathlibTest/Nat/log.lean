import Mathlib.Data.Nat.Log

/-!
These used to fail (ran out of heartbeats) but with a new faster `Nat.log`/`Nat.clog`, they succeed.
-/

set_option exponentiation.threshold 10000000

/-- info: 10000000 -/
#guard_msgs in
#eval Nat.log 2 (2 ^ 10000000 + 1)

/-- info: 10000001 -/
#guard_msgs in
#eval Nat.clog 2 (2 ^ 10000000 + 1)

/-- info: 10000000 -/
#guard_msgs in
#reduce Nat.log 2 (2 ^ 10000000 + 1)

/-- info: 10000001 -/
#guard_msgs in
#reduce Nat.clog 2 (2 ^ 10000000 + 1)
