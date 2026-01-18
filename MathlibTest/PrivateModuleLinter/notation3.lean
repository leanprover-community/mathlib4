module

import all Mathlib.Tactic.Linter.PrivateModule
import Mathlib.Util.Notation3

open Lean

local notation3 "MyList[" (x", "* => foldr (a b => List.cons a b) List.nil) "]" => x

/- Check that we have indeed created declarations, and aren't not linting just due to being an
empty file: -/
/--
info: [_private.MathlibTest.PrivateModuleLinter.notation3.0.«_aux_MathlibTest_PrivateModuleLinter_notation3___delab_app__private_MathlibTest_PrivateModuleLinter_notation3_0_termMyList[_,]_2»,
 _private.MathlibTest.PrivateModuleLinter.notation3.0.«termMyList[_,]»,
 _private.MathlibTest.PrivateModuleLinter.notation3.0.«_aux_MathlibTest_PrivateModuleLinter_notation3___delab_app__private_MathlibTest_PrivateModuleLinter_notation3_0_termMyList[_,]_1»,
 _private.MathlibTest.PrivateModuleLinter.notation3.0.«_aux_MathlibTest_PrivateModuleLinter_notation3___macroRules__private_MathlibTest_PrivateModuleLinter_notation3_0_termMyList[_,]_1»]
-/
#guard_msgs in
run_cmd do
  logInfo m!"{(← getEnv).constants.map₂.toArray.map (·.1)}"

-- The linter should fire since the `notation3` is local
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
