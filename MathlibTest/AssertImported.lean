module

-- Also explicitly import all dependencies, since `Mathlib` intentionally avoids importing
-- internals of some of the dependencies. For example:
-- ImportGraph asserts Lake.Workspace is not imported, but Mathlib doesn't import it either.
public import Aesop
public import Batteries
public import Lake
public import Lean
public import Mathlib
public import Plausible
public import ProofWidgets
public import Qq
public import Std

/-
This file checks that every declaration and import that have been flagged with
`assert_not_exists` or `assert_not_imported` is present in the environment once
all of `Mathlib` is available.
-/

#check_assertions!
