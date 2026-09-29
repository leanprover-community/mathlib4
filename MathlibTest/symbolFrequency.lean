import Mathlib

#adaptation_note /-- This test is disabled until lean4#15392 is fixed.
Since v4.35.0-rc2, Lean builds the symbol frequency index on the first query in each process,
and with `import Mathlib` this test takes about 250 s.
Re-enable it after the toolchain bump that includes the fix.
See https://github.com/leanprover/lean4/issues/15392
and https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/lean4.2315159.20causes.20significant.20regression.20in.20MathlibTests/with/627571608
-/

-- open Lean LibrarySuggestions

-- -- Check that the symbol frequency extension is working in Mathlib.
-- -- There should be at least 10_000 theorems mentioning `Nat`.

-- /-- info: true -/
-- #guard_msgs in
-- run_meta do
--   let n ← symbolFrequency `Nat
--   logInfo s!"{decide (10_000 ≤ n)}"
