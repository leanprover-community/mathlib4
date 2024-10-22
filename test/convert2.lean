import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Ring.Nat
import Mathlib.Tactic.Convert

set_option linter.unreachableTactic false

-- Prior to #7945 this failed with `(kernel) declaration has metavariables '_example'`.
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs (error) in
example (_h₁ : ((List.range 128).map (fun _ => 0)).sum = 0) : 0 ∣ 1 := by
  apply Nat.dvd_of_mul_dvd_mul_left Nat.zero_lt_one
  convert Nat.dvd_mul_left 0 1
