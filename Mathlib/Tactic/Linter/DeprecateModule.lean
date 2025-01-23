/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

/-!
#  The "deprecateModule" linter

The "deprecateModule" linter emits a warning when a file that has been renamed or split
is imported.

The usage is as follows. Write
```lean
import B
...
import Z

deprecate_module since yyyy-mm-dd
```
in module `A` with the expectation that `A` contains nothing else.
This triggers the `deprecateModule` linter to notify every file with `import A`
to instead import the *direct imports* of `A`, that is `B,...,Z`.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The `deprecateModule` linter emits a warning when a file that has been renamed or split
is imported.
The default value is `true`, since this linter is designed to warn projects downstream of `Mathlib`
of refactors and deprecations in `Mathlib` itself.
-/
register_option linter.deprecateModule : Bool := {
  defValue := true
  descr := "enable the deprecateModule linter"
}

/--
Defines the `deprecateModuleExt` extension for adding a `HashSet` of pairs of
* a module `Name` that has been deprecated and
* an array of `Name`s of modules that should be imported instead

to the environment.
-/
initialize deprecateModuleExt :
    SimplePersistentEnvExtension (Name × Array Name) (Std.HashSet (Name × Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addModuleDeprecation` adds to the `deprecateModuleExt` extension the pair consisting of the
current module name and the array of its direct imports.

It ignores the `Init` import, since this is a special module that is expected to be imported
by all files.
-/
def addModuleDeprecation {m : Type → Type} [Monad m] [MonadEnv m] [MonadQuotation m] : m Unit := do
  modifyEnv (deprecateModuleExt.addEntry ·
    (← getMainModule, (← getEnv).imports.filterMap fun i =>
      if i.module == `Init then none else i.module))

/--
`deprecate_module since yyyy-mm-dd` deprecates the current module `A` in favour of
its direct imports.
This means that any file that directly imports `A` will get a notification on the `import A` line
suggesting to instead import the *direct imports* of `A`.
-/
elab (name := deprecate_modules)
    "deprecate_module " &"since " yyyy:num "-" mm:num "-" dd:num : command => do
  if yyyy.getNat < 2025 then
    throwErrorAt yyyy "The year should be at least 2025!"
  if mm.getNat == 0 || 12 < mm.getNat || mm.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt mm "The month should be of the form 01, 02, ..., 12!"
  if dd.getNat == 0 || 31 < dd.getNat || dd.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt dd "The day should be of the form 01, 02, ..., 31!"
  addModuleDeprecation
  -- disable the linter, so that it does not complain in the file with the deprecation
  elabCommand (← `(set_option linter.deprecateModule false))

/-- A utility function to show the pairings `(deprecatedModule, #[preferredModules])`. -/
elab "show_deprecated_modules" : command => do
  let directImports := deprecateModuleExt.getState (← getEnv)
  logInfo <| "\n".intercalate <|
    directImports.fold (init := ["Deprecated modules\n"]) fun nms (i, deps) =>
      nms ++ [s!"'{i}' deprecates to\n{deps}\n"]

namespace DeprecateModule

@[inherit_doc Mathlib.Linter.linter.deprecateModule]
def deprecateModuleLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.deprecateModule (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mainModule ← getMainModule
  -- `Mathlib.lean` and `Mathlib/Tactic.Lean` are allowed to import deprecated files,
  -- since they (are expected to) import all modules in certain directories.
  if #[`Mathlib, `Mathlib.Tactic].contains mainModule then return
  if stx.isOfKind ``Linter.deprecate_modules then return
  let fm ← getFileMap
  let md := (getMainModuleDoc (← getEnv)).toArray
  -- The end of the first module doc-string, or the end of the file if there is none.
  let firstDocModPos := match md[0]? with
                          | none     => fm.positions.back!
                          | some doc => fm.ofPosition doc.declarationRange.endPos
  unless stx.getTailPos?.getD default ≤ firstDocModPos do
    return
  -- We try to parse the file up to `firstDocModPos`.
  let upToStx ← parseUpToHere firstDocModPos <|> (do
    -- If parsing failed, there is some command which is not a module docstring.
    -- In that case, we parse until the end of the modules and add an extra `section` afterwards,
    -- so we trigger a "no module doc-string" warning.
    let fil ← getFileName
    let (stx, _) ← Parser.parseHeader { input := fm.source, fileName := fil, fileMap := fm }
    parseUpToHere (stx.getTailPos?.getD default) "\nsection")
  let importIds := getImportIds upToStx
  let modulesWithNames := importIds.map fun i => (i, i.getId)
  let deprecations := deprecateModuleExt.getState (← getEnv)
  for is@(i, undeprecated) in deprecations do
    if let some (nmStx, _) := modulesWithNames.find? (·.2 == i) then
      Linter.logLint linter.deprecateModule nmStx
        m!"'{nmStx}' has been deprecated: please replace this import by \
          {"\nimport ".intercalate <| "\n" :: (undeprecated.map (·.toString)).toList}\n"

initialize addLinter deprecateModuleLinter

end DeprecateModule

end Mathlib.Linter
