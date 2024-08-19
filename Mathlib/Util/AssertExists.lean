/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison
-/
import Mathlib.Init
import Lean.Elab.Command
import Mathlib.Util.Attr

/-!
# User commands for assert the (non-)existence of declaration or instances.

These commands are used to enforce the independence of different parts of mathlib.

## TODO

Potentially after the port reimplement the mathlib 3 linters to check that declarations asserted
about do eventually exist.

Implement `assert_instance` and `assert_no_instance`
-/

section
open Lean Elab Meta Command

namespace Mathlib.AssertNotExist

open Lean Elab Command
elab "finalize_assertions" : command => do
  let env ← getEnv
  let ext := assertExistsExt.getState env
  let mut msgs : HashSet String := {}
  for d in ext do
    let msg (txt : String) :=
      s!"The {txt} '{d.givenName}' was required to not exist in '{d.modName}'.\n\
        This message means that the {txt} actually *never* exists."
    if d.isDecl && !env.contains d.givenName then
      msgs := msgs.insert (msg "declaration")
    else if !d.isDecl && !env.allImportedModuleNames.contains d.givenName then
      msgs := msgs.insert (msg "module")
  for msg in msgs do
    logWarning m!"{msg}"

/--
`addDeclEntry isDecl declName` takes as input the `Bool`ean `isDecl` and the `Name` `declName`.
It adds to the environment a new private declaration with a fresh name `freshName` and extends the
`AssertExists` environment extension with the data `isDecl, freshName, declName, currentModuleName`.
This information is used by the `assertExists` linter to capture declarations and modules that
are required to now exist/be imported at some point, but should eventually exist/be imported.
-/
def addDeclEntry (isDecl : Bool) (declName : Name) : CommandElabM Unit := do
  let modName ← getMainModule
  modifyEnv fun env =>
    assertExistsExt.addEntry env
      { isDecl := isDecl, givenName := declName, modName := modName }

end Mathlib.AssertNotExist

open Mathlib.AssertNotExist
/--
`assert_exists n` is a user command that asserts that a declaration named `n` exists
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).
-/
elab "assert_exists " n:ident : command => do
  -- this throws an error if the user types something ambiguous or
  -- something that doesn't exist, otherwise succeeds
  let _ ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n

/--
`assert_not_exists n` is a user command that asserts that a declaration named `n` *does not exist*
in the current import scope.

Be careful to use names (e.g. `Rat`) rather than notations (e.g. `ℚ`).

It may be used (sparingly!) in mathlib to enforce plans that certain files
are independent of each other.

If you encounter an error on an `assert_not_exists` command while developing mathlib,
it is probably because you have introduced new import dependencies to a file.

In this case, you should refactor your work
(for example by creating new files rather than adding imports to existing files).
You should *not* delete the `assert_not_exists` statement without careful discussion ahead of time.

`assert_not_exists` statements should generally live at the top of the file, after the module doc.
-/
elab "assert_not_exists " n:ident : command => do
  let decl ← ((liftCoreM <| realizeGlobalConstNoOverloadWithInfo n) <|> return .anonymous)
  if decl == .anonymous then
    addDeclEntry true n.getId
  else
  let env ← getEnv
  let c ← mkConstWithLevelParams decl
  let msg ← (do
    let mut some idx := env.getModuleIdxFor? decl
      | pure m!"Declaration {c} is defined in this file."
    let mut msg := m!"Declaration {c} is not allowed to be imported by this file.\n\
      It is defined in {env.header.moduleNames[idx.toNat]!},"
    for i in [idx.toNat+1:env.header.moduleData.size] do
      if env.header.moduleData[i]!.imports.any (·.module == env.header.moduleNames[idx.toNat]!) then
        idx := i
        msg := msg ++ m!"\n  which is imported by {env.header.moduleNames[i]!},"
    pure <| msg ++ m!"\n  which is imported by this file.")
  throw <| .error n m!"{msg}\n\n\
    These invariants are maintained by `assert_not_exists` statements, \
    and exist in order to ensure that \"complicated\" parts of the library \
    are not accidentally introduced as dependencies of \"simple\" parts of the library."

/-- `assert_not_imported m₁ m₂ ... mₙ` checks that each one of the modules `m₁ m₂ ... mₙ` is not
among the transitive imports of the current file.

The command does not currently check whether the modules `m₁ m₂ ... mₙ` actually exist.
-/
-- TODO: make sure that each one of `m₁ m₂ ... mₙ` is the name of an actually existing module!
elab "assert_not_imported " ids:ident+ : command => do
  let mods := (← getEnv).allImportedModuleNames
  for id in ids do
    if mods.contains id.getId then
      logWarningAt id m!"the module '{id}' is (transitively) imported"
    else
      addDeclEntry false id.getId

end
