import Mathlib

open Lean PremiseSelection

-- Check that the symbol frequency extension is working in Mathlib.
-- There should be at least 10_000 theorems mentioning `Nat`.

/-- info: true -/
#guard_msgs in
run_meta do
  let n ← symbolFrequency `Nat
  logInfo s!"{decide (10_000 ≤ n)}"
