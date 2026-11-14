module

public import Mathlib

meta import MathlibTest.NoDevToolProofs.Check

/-!
Check the complete exported environment for proofs from development-tool dependencies,
including generated theorems. This checks declarations materialized by importing `Mathlib`;
it does not force every possible lazily generated declaration.
-/

-- The restricted-package list. Enable further packages as their public exports are cleaned up.
run_cmd MathlibTest.NoDevToolProofs.assertNoPublicProofs #["importGraph"]
