import Mathlib

variable {K : Type*} [Field K] {x : K}

set_option maxHeartbeats 1500 in -- uses about 1000 as of 2025-09-10
/--
error: failed to synthesize
  Lean.Grind.NoNatZeroDivisors K

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Lean.Grind.NoNatZeroDivisors K

set_option maxHeartbeats 3000 in -- uses about 2500 as of 2025-09-10
example : x ^ 3 * x ^ 42 = x ^ 45 := by grind

-- This one is dismally slow (~0.5s, 18_000 heartbeats). However it doesn't affect `grind` directly.
set_option maxHeartbeats 20_000 in
/--
error: failed to synthesize
  NoZeroSMulDivisors ℕ K

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth NoZeroSMulDivisors ℕ K
