module

import Mathlib.Init
import all Mathlib.Tactic.Linter.PrivateModule
public import MathlibTest.PrivateModuleLinter.reservedName1

open Lean

-- `foo.eq_1` is still reserved:
/-- info: true -/
#guard_msgs in
run_cmd do
  logInfo m!"{isReservedName (← getEnv) ``foo.eq_1}"

-- `foo.eq_1` is not yet realized:
/-- info: reserved names: [] -/
#guard_msgs in
#show_new_reserved

-- realize `foo.eq_1`:
/--
info: @[defeq] theorem foo.eq_1 : foo = true :=
Eq.refl foo
-/
#guard_msgs in
#print foo.eq_1

-- Make sure `foo.eq_1` is in the local constants, and does not start with `_private`
/-- info: reserved names: [foo.eq_1] -/
#guard_msgs in
#show_new_reserved

-- The linter should fire despite the public name `foo.eq_1` being present
-- Run the linter on artificial `eoi` syntax so that we can actually guard the message
set_option linter.mathlibStandardSet true in
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
