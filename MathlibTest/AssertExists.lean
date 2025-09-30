import Mathlib.Util.AssertExists

/-- info: No assertions made. -/
#guard_msgs in
#check_assertions

#check_assertions!

assert_not_exists Nats

theorem Nats : True := .intro

/--
info:
✅️ 'Nats' (declaration) asserted in 'MathlibTest.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions

#check_assertions!

/--
warning: the module 'Lean.Elab.Command' is (transitively) imported via
Lean.Elab.Command,
  which is imported by Lean.Linter.Sets,
  which is imported by Mathlib.Init,
  which is imported by Mathlib.Util.AssertExistsExt,
  which is imported by Mathlib.Util.AssertExists,
  which is imported by this file.
-/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist

/--
warning:
✅️ 'Nats' (declaration) asserted in 'MathlibTest.AssertExists'.
❌️ 'I_do_not_exist' (module) asserted in 'MathlibTest.AssertExists'.
❌️ 'Mathlib.Tactic.Common' (module) asserted in 'MathlibTest.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions

/--
warning:
❌️ 'I_do_not_exist' (module) asserted in 'MathlibTest.AssertExists'.
❌️ 'Mathlib.Tactic.Common' (module) asserted in 'MathlibTest.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions!
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
  commandAssert_not_exists_
  I_do_not_exist
