import Mathlib.Util.AssertExists

/--
error: Declaration commandAssert_not_imported_ is not allowed to be imported by this file.
It is defined in Mathlib.Util.AssertExists,
  which is imported by this file.

These invariants are maintained by `assert_not_exists` statements, and exist in order to ensure that "complicated" parts of the library are not accidentally introduced as dependencies of "simple" parts of the library.
---
error: Declaration commandAssert_not_exists_ is not allowed to be imported by this file.
It is defined in Mathlib.Util.AssertExists,
  which is imported by this file.

These invariants are maintained by `assert_not_exists` statements, and exist in order to ensure that "complicated" parts of the library are not accidentally introduced as dependencies of "simple" parts of the library.
-/
#guard_msgs in
assert_not_exists
  commandAssert_not_imported_
  Rat
  commandAssert_not_exists_
  I_do_not_exist

/-- warning: the module 'Lean.Elab.Command' is (transitively) imported -/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist
