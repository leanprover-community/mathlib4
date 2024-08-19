/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command
import Batteries.Tactic.Lint.Basic

/-!
# The `AssertNot` environment extension and the `assertNot` environment linter
-/

open Lean

namespace Mathlib.Linter

/-- A `Label` is the main structure for converting a folder into a `t-`label.
* The `label` field is the actual GitHub label.
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labeled by `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.

It is not really intended to be used directly.
The command `add_label` manages `Label`s: it creates them and adds them to the `Environment`.
-/
structure AssertExists where
  /-- The fully qualified name of a declaration that is expected to exist. -/
  isDecl : Bool
  freshName : Name
  givenName : Name
  modName : Name

/-- Defines the `assertExistsExt` extension for adding an `Array` of `AssertExists`s
to the environment. -/
initialize assertExistsExt :
    PersistentEnvExtension AssertExists AssertExists (Array AssertExists) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := (pure <| .flatten ·)
    addEntryFn := .push
    exportEntriesFn := id
  }

/-- A linter for checking that declarations that were asserted to not exist in one module,
do exist somewhere. -/
@[env_linter] def Linter.AssertExists : Std.Tactic.Lint.Linter where
  noErrorsFound := "All declarations and modules that were expected to exist do actually exist."
  errorsFound := "DECLARATIONS AND MODULES THAT DO NOT EXIST BUT SHOULD EXIST:"
  test declName := do
    let env ← getEnv
    let ext := assertExistsExt.getState env
    if ext.isEmpty || declName.components.length ≤ 1 then return none
    let last2 := declName.components.drop (declName.components.length - 2)
    let declTail := last2[0]! ++ last2[1]!
    for d in ext do
      if d.freshName == declTail then
        let msg (txt : String) :=
          s!"The {txt} '{d.givenName}' was required to not exist in '{d.modName}'.\n\
            This message means that the {txt} actually *never* exists."
        if d.isDecl && !env.contains d.givenName then
          return some (msg "declaration")
        else if !d.isDecl && !env.allImportedModuleNames.contains d.givenName then
          return some (msg "module")
    return none

open Elab.Command in
/--
`addDeclEntry declName isDecl` takes as input the `Name` `declName` and the `Bool`ean `isDecl`.
It adds to the environment a new private declaration with a fresh name `freshName` and extends the
`AssertExists` environment extension with the data `isDecl, freshName, declName, currentModuleName`.
This information is used by the `assertExists` linter to capture declarations and modules that
are required to now exist/be imported at some point, but should eventually exist/be imported.
-/
def addDeclEntry (declName : Name) (isDecl : Bool) : CommandElabM Unit := do
  let nm ← liftCoreM do mkFreshId
  elabCommand (← `(private theorem $(mkIdent nm) : True := .intro))
  setEnv <| assertExistsExt.addEntry (← getEnv)
    { isDecl := isDecl, freshName := nm, givenName := declName, modName := ← getMainModule }

end Mathlib.Linter
