import Mathlib.Tactic.Find
theorem add_comm_zero {n} : 0 + n = n + 0 := Nat.add_comm _ _

-- These results are too volatile to test with `#guard_msgs`,
-- we just suppress them for now.

#guard_msgs (drop info) in
#find _ + _ = _ + _

#guard_msgs (drop info) in
#find ?n + _ = _ + ?n

#guard_msgs (drop info) in
#find (_ : Nat) + _ = _ + _

#guard_msgs (drop info) in
#find Nat → Nat

#guard_msgs (drop info) in
#find ?n ≤ ?m → ?n + _ ≤ ?m + _
