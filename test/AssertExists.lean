import Mathlib.Util.AssertExists

/-- info: No assertions made. -/
#guard_msgs in
#check_assertions

#check_assertions!

assert_not_exists Nats

theorem Nats : True := .intro

/--
info:
✅️ 'Nats' (declaration) asserted in 'test.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions

#check_assertions!

/-- warning: the module 'Lean.Elab.Command' is (transitively) imported -/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist

/--
warning:
✅️ 'Nats' (declaration) asserted in 'test.AssertExists'.
❌️ 'I_do_not_exist' (module) asserted in 'test.AssertExists'.
❌️ 'Mathlib.Tactic.Common' (module) asserted in 'test.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions

/--
warning:
❌️ 'I_do_not_exist' (module) asserted in 'test.AssertExists'.
❌️ 'Mathlib.Tactic.Common' (module) asserted in 'test.AssertExists'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions!
