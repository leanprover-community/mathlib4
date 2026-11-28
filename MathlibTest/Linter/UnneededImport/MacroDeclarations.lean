-- The macro of `MacroAux` declares a theorem that uses a constant of `LeafAux`, and the syntax
-- of the file never names that constant. The `declaredNames` producer supplies the declaration,
-- so the linter keeps both imports.
module

import MathlibTest.Linter.UnneededImport.MacroAux
import MathlibTest.Linter.UnneededImport.LeafAux
import Mathlib.Tactic.Linter.UnneededImport

/-! # An import that a macro-generated declaration uses -/

set_option linter.unneededImport true

declare_leaf_refl

/--
warning: using 'exit' to interrupt Lean
-/
#guard_msgs in
#exit
