/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

/-!
#  The "deprecated.module" linter

The "deprecated.module" linter emits a warning when a file that has been renamed or split
is imported.

The usage is as follows. Write
```lean
import B
...
import Z

deprecated_module since yyyy-mm-dd
```
in module `A` with the expectation that `A` contains nothing else.
This triggers the `deprecated.module` linter to notify every file with `import A`
to instead import the *direct imports* of `A`, that is `B,...,Z`.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The `deprecated.module` linter emits a warning when a file that has been renamed or split
is imported.
The default value is `true`, since this linter is designed to warn projects downstream of `Mathlib`
of refactors and deprecations in `Mathlib` itself.
-/
register_option linter.deprecated.module : Bool := {
  defValue := true
  descr := "enable the `deprecated.module` linter"
}

/--
Defines the `deprecatedModuleExt` extension for adding a `HashSet` of pairs of
* a module `Name` that has been deprecated and
* an array of `Name`s of modules that should be imported instead

to the environment.
-/
initialize deprecatedModuleExt :
    SimplePersistentEnvExtension (Name × Array Name) (Std.HashSet (Name × Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := (·.foldl Std.HashSet.insertMany {})
    addEntryFn := .insert
  }

/--
`addModuleDeprecation` adds to the `deprecatedModuleExt` extension the pair consisting of the
current module name and the array of its direct imports.

It ignores the `Init` import, since this is a special module that is expected to be imported
by all files.
-/
def addModuleDeprecation {m : Type → Type} [Monad m] [MonadEnv m] [MonadQuotation m] : m Unit := do
  modifyEnv (deprecatedModuleExt.addEntry ·
    (← getMainModule, (← getEnv).imports.filterMap fun i =>
      if i.module == `Init then none else i.module))

/--
`deprecated_module since yyyy-mm-dd` deprecates the current module `A` in favour of
its direct imports.
This means that any file that directly imports `A` will get a notification on the `import A` line
suggesting to instead import the *direct imports* of `A`.
-/
elab (name := deprecated_modules)
    "deprecated_module " &"since " yyyy:num "-" mm:num "-" dd:num : command => do
  if yyyy.getNat < 2025 then
    throwErrorAt yyyy "The year should be at least 2025!"
  if mm.getNat == 0 || 12 < mm.getNat || mm.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt mm "The month should be of the form 01, 02, ..., 12!"
  if dd.getNat == 0 || 31 < dd.getNat || dd.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt dd "The day should be of the form 01, 02, ..., 31!"
  addModuleDeprecation
  -- disable the linter, so that it does not complain in the file with the deprecation
  elabCommand (← `(set_option linter.deprecated.module false))

/-- A utility function to show the pairings `(deprecatedModule, #[preferredModules])`. -/
elab "#show_deprecated_modules" : command => do
  let directImports := deprecatedModuleExt.getState (← getEnv)
  logInfo <| "\n".intercalate <|
    directImports.fold (init := ["Deprecated modules\n"]) fun nms (i, deps) =>
      nms ++ [s!"'{i}' deprecates to\n{deps}\n"]

namespace DeprecatedModule

@[inherit_doc Mathlib.Linter.linter.deprecated.module]
def deprecated.moduleLinter : Linter where run := withSetOptionIn fun stx ↦ do
  let deprecations := deprecatedModuleExt.getState (← getEnv)
  if deprecations.isEmpty then
    return
  unless Linter.getLinterValue linter.deprecated.module (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mainModule ← getMainModule
  -- `Mathlib.lean` and `Mathlib/Tactic.Lean` are allowed to import deprecated files,
  -- since they (are expected to) import all modules in certain directories.
  if #[`Mathlib, `Mathlib.Tactic].contains mainModule then return
  if stx.isOfKind ``Linter.deprecated_modules then return
  let fm ← getFileMap
  let fil ← getFileName
  let (importStx, _) ← Parser.parseHeader { input := fm.source, fileName := fil, fileMap := fm }
  let importIds := getImportIds importStx
  let modulesWithNames := importIds.map fun i => (i, i.getId)
  for is@(i, undeprecated) in deprecations do
    for (nmStx, _) in modulesWithNames.filter (·.2 == i) do
      Linter.logLint linter.deprecated.module nmStx
        m!"'{nmStx}' has been deprecated: please replace this import by\n\n\
          {String.join <| (undeprecated.foldl (·.push s!"import {·}\n") #[]).toList}"

initialize addLinter deprecated.moduleLinter

end DeprecatedModule

end Mathlib.Linter
