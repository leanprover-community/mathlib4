-- The file uses the notation of `NotationAux` and no constant of that module reaches the
-- environment, so only the syntax kinds of the command show the use. The linter keeps the
-- import and reports the unused `LeafAux` import.
module

import MathlibTest.Linter.UnneededImport.NotationAux
import MathlibTest.Linter.UnneededImport.LeafAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # An import that provides only syntax -/

set_option linter.unneededImport true

example : Nat := unneededImportAuxOne

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.LeafAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
