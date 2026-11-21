-- A `set_option` of an option that `OptionAux` declares is the only reference of the file to
-- that module, so the linter keeps the import. It reports the unused `LeafAux` import.
module

import MathlibTest.Linter.UnneededImport.OptionAux
import MathlibTest.Linter.UnneededImport.LeafAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # An import that only a `set_option` uses -/

set_option linter.unneededImport true
set_option mathlibTest.unneededImportAux true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.LeafAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
