import Mathlib.Util.AssertExists

/-- warning: the module 'Lean.Elab.Command' is (transitively) imported -/
#guard_msgs in
assert_not_imported
  Mathlib.Tactic.Common
  Lean.Elab.Command
  I_do_not_exist
