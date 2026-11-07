-- The linter reports a direct import that a sibling direct import covers: the import closure of
-- `Mathlib.Tactic.Linter.UnneededImport` contains `Mathlib.Tactic.Linter.DeclaredNames`.
module

import Mathlib.Tactic.Linter.DeclaredNames
import Mathlib.Tactic.Linter.UnneededImport

/-! # A direct import that a sibling import covers -/

set_option linter.unneededImport true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'Mathlib.Tactic.Linter.DeclaredNames' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; the closure does not change: the other imports cover all of it

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
