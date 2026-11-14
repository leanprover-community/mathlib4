-- The count in the report covers the whole closure of the import, not the import alone: the
-- removal of `ChainAux` drops `ChainAux` and `LeafAux`.
module

import MathlibTest.Linter.UnneededImport.ChainAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # A removal that drops several modules -/

set_option linter.unneededImport true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.ChainAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 2 modules from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
