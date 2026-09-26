-- The report states the effect of the removal on the import closure. `ChainAux` imports
-- `LeafAux`, so the direct import of `LeafAux` leaves the closure unchanged, and the removal of
-- `ChainAux` drops one module.
module

import MathlibTest.Linter.UnneededImport.LeafAux
import MathlibTest.Linter.UnneededImport.ChainAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # The closure impact of a removal -/

set_option linter.unneededImport true

/--
warning: using 'exit' to interrupt Lean
---
warning: import 'MathlibTest.Linter.UnneededImport.LeafAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; the closure does not change: the other imports cover all of it

Note: This linter can be disabled with `set_option linter.unneededImport false`
---
warning: import 'MathlibTest.Linter.UnneededImport.ChainAux' is possibly unneeded: the other imports cover every constant that this file uses from its import closure; removing it also drops 1 module from the import closure

Note: This linter can be disabled with `set_option linter.unneededImport false`
-/
#guard_msgs in
#exit
