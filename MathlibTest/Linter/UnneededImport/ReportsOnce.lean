-- The report fires once per file: a second terminal command produces no further report.
module

import MathlibTest.Linter.UnneededImport.LeafAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # One report per file -/

set_option linter.unneededImport true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.LeafAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit

/-- warning: using 'exit' to interrupt Lean -/
#guard_msgs in
#exit
