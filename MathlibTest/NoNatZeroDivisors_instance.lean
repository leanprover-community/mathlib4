import Mathlib

variable {K : Type*} [Field K]

-- This is far too slow as is, and this test guards against it getting worse.
set_option maxHeartbeats 19000 in
/--
error: failed to synthesize
  Lean.Grind.NoNatZeroDivisors K

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Lean.Grind.NoNatZeroDivisors K
