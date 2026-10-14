import Mathlib
-- Also explicitly import all dependencies, since `Mathlib` intentionally avoids importing
-- internals of some of the dependencies. For example:
-- ImportGraph asserts Lake.Workspace is not imported, but Mathlib doesn't import it either.
import Aesop
import Batteries
import Lake
import Lean
import Plausible
import ProofWidgets
import Qq
import Std

-- ImportGraph asserts Lake.Workspace is not imported, but Mathlib doesn't import it either.
-- So import it for the sake of testing.
import Lake.Config.Workspace

/-
This file checks that every declaration and import that have been flagged with
`assert_not_exists` or `assert_not_imported` is present in the environment once
all of `Mathlib` is available.
-/

#check_assertions!
