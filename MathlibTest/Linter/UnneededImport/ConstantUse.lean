-- A declaration of the file uses a constant of `LeafAux`, and no other import covers that
-- module, so the linter keeps the import. It reports the unused `NotationAux` import.
module

import MathlibTest.Linter.UnneededImport.LeafAux
import MathlibTest.Linter.UnneededImport.NotationAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # An import that a declaration uses -/

set_option linter.unneededImport true

theorem usesLeafValue :
    MathlibTest.UnneededImport.leafValue = MathlibTest.UnneededImport.leafValue := rfl

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.NotationAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
