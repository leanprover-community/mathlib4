module

import Mathlib.Init
import all Mathlib.Tactic.Linter.PrivateModule
import Lean.Elab.Command

open Lean

set_option linter.mathlibStandardSet true

theorem foo : True := trivial

def bar : Bool := true

-- Run the linter on artificial `eoi` syntax so that we can actually guard the message
open Mathlib.Linter Parser in
/--
warning: The current module only contains private declarations.

Consider adding `@[expose] public section` at the beginning of the module, or selectively marking declarations as `public`.

Note: This linter can be disabled with `set_option linter.privateModule false`
-/
#guard_msgs in
run_cmd do
  let eoi := mkNode ``Command.eoi #[mkAtom .none ""]
  privateModule.run eoi

-- Disable so that this test is silent
set_option linter.privateModule false
