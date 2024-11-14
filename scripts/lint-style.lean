/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.ParseImportsFast
import Batteries.Data.String.Basic
import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This file defines the `lint-style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.

In addition, this checks that
- `Mathlib.Init` is (transitively) imported in all of mathlib, and
- every file in `scripts` is documented in its top-level README.
-/

open Cli Mathlib.Linter.TextBased System.FilePath

/-- Parse all imports in a text file at `path` and return just their names:
this is just a thin wrapper around `Lean.parseImports'`.
Omit `Init (which is part of the prelude). -/
def findImports (path : System.FilePath) : IO (Array Lean.Name) := do
  return (← Lean.parseImports' (← IO.FS.readFile path) path.toString)
    |>.map (fun imp ↦ imp.module) |>.erase `Init


/-- Check that `Mathlib.Init` is transitively imported in all of Mathlib.

Every file imported in `Mathlib.Init` should in turn import the `Header` linter
(except for the header linter itself, of course).
Return `true` iff there was an error.
-/
def checkInitImports : IO Bool := do
  -- Find any file in the Mathlib directory which does not contain any Mathlib import.
  -- We simply parse `Mathlib.lean`, as CI ensures this file is up to date.
  let allModuleNames := (← findImports "Mathlib.lean").erase `Batteries
  let mut modulesWithoutMathlibImports := #[]
  let mut importsHeaderLinter := #[]
  for module in allModuleNames do
    let path := System.mkFilePath (module.components.map fun n ↦ n.toString)|>.addExtension "lean"
    let imports ← findImports path
    let hasNoMathlibImport := imports.all fun name ↦ name.getRoot != `Mathlib
    if hasNoMathlibImport then
      modulesWithoutMathlibImports := modulesWithoutMathlibImports.push module
    if imports.contains `Mathlib.Tactic.Linter.Header then
      importsHeaderLinter := importsHeaderLinter.push module

  -- Every file importing the `header` linter should be imported in `Mathlib/Init.lean` itself.
  -- (Downstream files should import `Mathlib.Init` and not the header linter.)
  -- The only exception are auto-generated import-only files.
  let initImports ← findImports ("Mathlib" / "Init.lean")
  let mismatch := importsHeaderLinter.filter (fun mod ↦
    ![`Mathlib, `Mathlib.Tactic, `Mathlib.Init].contains mod && !initImports.contains mod)
    -- This file is transitively imported by `Mathlib.Init`.
    |>.erase `Mathlib.Tactic.DeclarationNames
  if mismatch.size > 0 then
    IO.eprintln s!"error: the following {mismatch.size} module(s) import the `header` linter \
      directly, but should import Mathlib.Init instead: {mismatch}\n\
      The `header` linter is included in Mathlib.Init, and every file in Mathlib \
      should import Mathlib.Init.\nPlease adjust the imports accordingly."
    return true

  -- Now, it only remains to check that every module (except for the Header linter itself)
  -- imports some file in Mathlib.
  let missing := modulesWithoutMathlibImports.erase `Mathlib.Tactic.Linter.Header
  if missing.size > 0 then
    IO.eprintln s!"error: the following {missing.size} module(s) do not import Mathlib.Init: \
      {missing}"
    return true
  return false


/-- Verifies that every file in the `scripts` directory is documented in `scripts/README.md`.
Return `True` if there are undocumented scripts, otherwise `False`. -/
def allScriptsDocumented : IO Bool := do
  -- Retrieve all scripts (except for the `bench` directory).
  let allScripts ← (walkDir "scripts" fun p ↦ pure (p.components.getD 1 "" != "bench"))
  let allScripts := allScripts.erase ("scripts" / "bench")|>.erase ("scripts" / "README.md")
  -- Check if the README text contains each file enclosed in backticks.
  let readme : String ← IO.FS.readFile ("scripts" / "README.md")
  -- These are data files for linter exceptions: don't complain about these *for now*.
  let dataFiles := #["noshake.json", "nolints-style.txt"]
  -- For now, there are no scripts in sub-directories that should be documented.
  let fileNames := allScripts.map (·.fileName.get!)
  let undocumented := fileNames.filter fun script ↦
    !readme.containsSubstr s!"`{script}`" && !dataFiles.contains script
  if undocumented.size > 0 then
    IO.println s!"error: found {undocumented.size} undocumented script(s): \
      please describe the script(s) in 'scripts/README.md'\n  \
      {String.intercalate "," undocumented.toList}"
  return undocumented.size == 0


/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let style : ErrorFormat := match args.hasFlag "github" with
    | true => ErrorFormat.github
    | false => ErrorFormat.humanReadable
  let fix := args.hasFlag "fix"
  -- Read all module names to lint.
  let mut allModuleNames := #[]
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    allModuleNames := allModuleNames.append (← findImports s)
  -- Note: since "Batteries" is added explicitly to "Mathlib.lean", we remove it here manually.
  allModuleNames := allModuleNames.erase `Batteries
  let mut numberErrors ← lintModules allModuleNames style fix
  if ← checkInitImports then numberErrors := numberErrors + 1
  if !(← allScriptsDocumented) then numberErrors := numberErrors + 1
  -- If run with the `--fix` argument, return a zero exit code.
  -- Otherwise, make sure to return an exit code of at most 125,
  -- so this return value can be used further in shell scripts.
  if args.hasFlag "fix" then
    return 0
  else return min numberErrors 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
-- so far, no help options or so: perhaps that is fine?
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    fix;        "Automatically fix the style error, if possible"
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
