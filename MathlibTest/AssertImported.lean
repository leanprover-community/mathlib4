import Mathlib

/-
This file checks that every declaration and import that have been flagged with
`assert_not_exists` or `assert_not_imported` is present in the environment once
all of `Mathlib` is available.
-/

#check_assertions!
