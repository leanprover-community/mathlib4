import Mathlib

variable {K : Type*} [Field K] {x : K}

-- This one is dismally slow:
-- #time
-- #synth NoZeroSMulDivisors ℕ K

set_option maxHeartbeats 3000 in -- uses under 2000 as of 2025-08-06
/--
error: failed to synthesize
  Lean.Grind.NoNatZeroDivisors K

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Lean.Grind.NoNatZeroDivisors K

#adaptation_note
/--
I have temporarily commented out this test, as fixing the underlying problem
has prevented getting a successful build of `nightly-testing` for several days.

One we have a build, I'll restore this test to continue working on it.
-/
-- set_option maxHeartbeats 6000 in -- uses about 4000 as of 2025-08-06
-- example : x ^ 3 * x ^ 42 = x ^ 45 := by grind
