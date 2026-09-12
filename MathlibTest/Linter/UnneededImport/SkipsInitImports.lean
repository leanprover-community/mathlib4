-- The linter never reports `Mathlib.Init` or a module of the `Init` root: every file carries
-- those imports by convention. It reports the unused `LeafAux` import of this file.
module

import Init.Data.List.Lemmas
import Mathlib.Init
import MathlibTest.Linter.UnneededImport.LeafAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # Imports that the linter skips -/

set_option linter.unneededImport true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.LeafAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
