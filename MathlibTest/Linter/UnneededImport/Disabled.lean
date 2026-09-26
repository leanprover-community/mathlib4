-- The linter is disabled by default: this file has a redundant import and produces no report.
module

import Mathlib.Tactic.Linter.DeclaredNames
import Mathlib.Tactic.Linter.UnneededImport

/-! # The linter stays silent when the option is off -/

/--
warning: using 'exit' to interrupt Lean
-/
#guard_msgs in
#exit
