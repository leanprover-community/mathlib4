/-
Copyright (c) 2025 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Init

/-!
#  The "importDeprecation" linter

The "importDeprecation" linter emits a warning when a file that has been renamed or split
is imported.
-/

open Lean Elab Command

namespace Mathlib.Linter

/--
The "importDeprecation" linter emits a warning when a file that has been renamed or split
is imported.
-/
register_option linter.importDeprecation : Bool := {
  defValue := true
  descr := "enable the importDeprecation linter"
}

/--
Defines the `deprecatedImportsExt` extension for adding a `HashSet` of module `Name`s
to the environment.
-/
initialize deprecatedImportsExt :
    SimplePersistentEnvExtension (Name × Array Name) (Std.HashSet (Name × Array Name)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Std.HashSet.insertMany {}
    addEntryFn := .insert
  }

/--
`addModuleDeprecation modName` takes as input the module `Name` `modName` and adds it to the
`deprecatedImportsExt` extension.
-/
def addModuleDeprecation {m : Type → Type} [Monad m] [MonadEnv m] [MonadQuotation m] : m Unit := do
  modifyEnv (deprecatedImportsExt.addEntry ·
    (← getMainModule, (← getEnv).imports.filterMap fun i =>
      if i.module == `Init then none else (i.module)))

/--
`deprecate_imports since yyyy-mm-dd` deprecates the imports of the current file.
This means that any file that imports the current file will get a notification
on the corresponding import line suggesting which file/files to import instead.
-/
elab (name := deprecate_imports)
    "deprecate_imports " &"since" yyyy:num "-" mm:num "-" dd:num: command => do
  if yyyy.getNat < 2025 then
    throwErrorAt yyyy "The year should be at least 2025!"
  if mm.getNat == 0 || 12 < mm.getNat || mm.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt mm "The month should be of the form 01, 02,..., 12!"
  if dd.getNat == 0 || 31 < dd.getNat || dd.raw.getSubstring?.get!.toString.trim.length != 2 then
    throwErrorAt dd "The day should be of the form 01, 02,..., 31!}"
  addModuleDeprecation
  -- disable the linter, so that it does not complain in the file with the deprecation
  elabCommand (← `(set_option linter.importDeprecation false))

/-- A utility function to show the pairings `(deprecatedModule, #[preferredModules])`. -/
elab "show_deprecated_imports" : command => do
  let directImports := deprecatedImportsExt.getState (← getEnv)
  logInfo <| "\n".intercalate <|
    directImports.fold (init := ["Deprecated modules\n"]) fun nms (i, deps) =>
      nms ++ [s!"'{i}' deprecates to\n{deps}\n"]

namespace ImportDeprecation

@[inherit_doc Mathlib.Linter.linter.importDeprecation]
def importDeprecationLinter : Linter where run := withSetOptionIn fun stx ↦ do
  unless Linter.getLinterValue linter.importDeprecation (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mainModule ← getMainModule
  unless Linter.getLinterValue linter.style.header (← getOptions) do
    return
  if (← get).messages.hasErrors then
    return
  -- The imports of `Mathlib.lean` and `Mathlib.Tactic` are not required to be non-deprecated,
  -- since these files are expected to import all modules satisfying certain path-restrictions.
  if #[`Mathlib, `Mathlib.Tactic].contains mainModule then return
  if stx.isOfKind ``Linter.deprecate_imports then return
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
    -- In that case, we parse until the end of the imports and add an extra `section` afterwards,
    -- so we trigger a "no module doc-string" warning.
    let fil ← getFileName
    let (stx, _) ← Parser.parseHeader { input := fm.source, fileName := fil, fileMap := fm }
    parseUpToHere (stx.getTailPos?.getD default) "\nsection")
  let importIds := getImportIds upToStx
  let importsWithNames := importIds.map fun i => (i, i.getId)
  let deprecations := deprecatedImportsExt.getState (← getEnv)
  for is@(i, _) in deprecations do
    match importsWithNames.find? (·.2 == i) with
      | none => continue
      | some x =>
        let ((_, undeprecated), (nmStx, _)) := (is, x)
        Linter.logLint linter.importDeprecation nmStx
          m!"'{nmStx}' has been deprecated: please replaced this import by \
            {"\nimport ".intercalate <| "\n" :: (undeprecated.map (·.toString)).toList}\n"

initialize addLinter importDeprecationLinter

end ImportDeprecation

end Mathlib.Linter
