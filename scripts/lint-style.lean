/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Basic
import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This files defines the `lint-style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.

In addition, this checks that `Mathlib.Init` is (transitively) imported in all of mathlib.
-/

open Cli Mathlib.Linter.TextBased

/-- Check that `Mathlib.Init` is transitively imported in all of Mathlib. -/
def checkInitImports : IO Bool := do
  -- First, we find any file in the Mathlib directory which does not contain
  -- any Mathlib import, i.e. no line starting with "import Mathlib".
  -- This is not absolutely error-proof (for instance, would not detect a multi-line
  -- comment containing the line import Mathlib), but is good enough in practice.
  let mut modulesWithoutMathlibImports := #[]
  -- We simply parse Mathlib.lean; this avoids any need for external tools like grep.
  let allModules := (← IO.FS.lines "Mathlib.lean").map (fun line ↦ line.stripPrefix "import ")
    |>.filter (fun module ↦ module.startsWith "Mathlib")
    --|>.map (fun module ↦ (System.mkFilePath (module.split (· == '.'))).addExtension "lean")
  for module in allModules do
    let path := (System.mkFilePath (module.split (· == '.'))).addExtension "lean"
    let hasMathlibImport := (← IO.FS.lines path).any fun s ↦ s.startsWith "import Mathlib"
    if !hasMathlibImport then
      modulesWithoutMathlibImports := modulesWithoutMathlibImports.push module

  -- We check that each of these is imported in Mathlib.Init.
  let imports := (← IO.FS.lines "Mathlib/Init.lean").filter (fun s ↦ s.startsWith "import ")
    |>.map (fun s ↦ s.stripPrefix "import ")
  let missing := modulesWithoutMathlibImports.filter (fun mod ↦ !imports.contains mod)
    -- `DeclarationNames` is imported transitively; we manually allow this
    |>.erase "Mathlib.Tactic.DeclarationNames"
  if missing.size > 0 then
    IO.eprintln s!"error: the following {missing.size} modules are not imported in Mathlib.Init: \
    {missing}"
    return True

  -- Secondly, after #18725 almost all files imported in Mathlib.Init import the `header` linter
  -- defined in `Mathlib.Tactic.Linter.Header`: so, we verify that the only
  -- files importing `Mathlib.Tactic.Linter.Header` are also imported in `Mathlib.Init`.
  let mut modulesImportingHeaderLinter := #[]
  for module in allModules do
    let path := (System.mkFilePath (module.split (· == '.'))).addExtension "lean"
    let importsHeaderLinter := (← IO.FS.lines path).contains "import Mathlib.Tactic.Linter.Header"
    if importsHeaderLinter then
      modulesImportingHeaderLinter := modulesImportingHeaderLinter.push module
  let mismatch := modulesImportingHeaderLinter.filter
    (fun mod ↦ !["Mathlib", "Mathlib.Tactic", "Mathlib.Init"].contains mod && !imports.contains mod)
  if mismatch.size > 0 then
    IO.eprintln s!"error: the following {mismatch.size} modules import the `header` linter directly,
      but are not imported in Mathlib.Init: {missing}\n
      If your module imports Mathlib.Init, there is no need for this import; please remove it."
    return True
  return False


/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let style : ErrorFormat := match args.hasFlag "github" with
    | true => ErrorFormat.github
    | false => ErrorFormat.humanReadable
  let fix := args.hasFlag "fix"
  -- Read all module names to lint.
  let mut allModules := #[]
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    allModules := allModules.append ((← IO.FS.lines s).map (·.stripPrefix "import "))
  -- note: since we manually add "Batteries" to "Mathlib.lean", we remove it here manually
  allModules := allModules.erase "Batteries"
  let mut numberErrors := ← lintModules allModules style fix
  if ← checkInitImports then numberErrors := numberErrors + 1
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
