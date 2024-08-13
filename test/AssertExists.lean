import Mathlib.Util.AssertExists

/--
warning: 'Lean.Elab.Command' is imported
---
warning: 'I_do_not_exist' does not exist
-/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist
