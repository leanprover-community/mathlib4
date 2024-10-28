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
  -- Find any file in the Mathlib directory which does not contain any Mathlib import.
  -- The current check (for any line starting with "import Mathlib") is not perfect
  -- (for instance, it would detect a multi-line comment containing the line import Mathlib),
  -- but is good enough in practice.
  let mut modulesWithoutMathlibImports := #[]
  -- We simply parse `Mathlib.lean`; this removes the need for external tools like grep.
  let allModules := (← IO.FS.lines "Mathlib.lean").map (·.stripPrefix "import ")
    |>.filter (·.startsWith "Mathlib")
  for module in allModules do
    let path := (System.mkFilePath (module.split (· == '.'))).addExtension "lean"
    let hasMathlibImport := (← IO.FS.lines path).any fun s ↦ s.startsWith "import Mathlib"
    if !hasMathlibImport then
      modulesWithoutMathlibImports := modulesWithoutMathlibImports.push module

  -- We check that each of these is imported in `Mathlib/Init.lean`.
  let initImports := (← IO.FS.lines "Mathlib/Init.lean").filter (·.startsWith "import ")
    |>.map (·.stripPrefix "import ")
  let missing := modulesWithoutMathlibImports.filter (fun mod ↦ !initImports.contains mod)
    -- `DeclarationNames` is imported transitively in `Mathlib/Init.lean`.
    |>.erase "Mathlib.Tactic.DeclarationNames"
  if missing.size > 0 then
    IO.eprintln s!"error: the following {missing.size} module(s) do not import Mathlib.Init: \
      {missing}"
    return True

  -- Secondly, after #18725 almost all files imported in Mathlib.Init import the `header` linter
  -- defined in `Mathlib.Tactic.Linter.Header`: so, we verify that the only
  -- files importing `Mathlib.Tactic.Linter.Header` are also imported in `Mathlib.Init`.
  let mut modulesImportingHeaderLinter := #[]
  for module in allModules do
    let path := (System.mkFilePath (module.split (· == '.'))).addExtension "lean"
    if (← IO.FS.lines path).contains "import Mathlib.Tactic.Linter.Header" then
      modulesImportingHeaderLinter := modulesImportingHeaderLinter.push module
  let mismatch := modulesImportingHeaderLinter.filter (fun mod ↦
    !["Mathlib", "Mathlib.Tactic", "Mathlib.Init"].contains mod && !initImports.contains mod)
  if mismatch.size > 0 then
    IO.eprintln s!"error: the following {mismatch.size} module(s) import the `header` linter \
      directly, but also import Mathlib.Init: {mismatch}\n\
      The `header` linter is already imported in Mathlib.Init; there is no need to import it \
      again.\nPlease remove the import of `Mathlib.Tactic.Linter.Header."
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
  let mut numberErrors ← lintModules allModules style fix
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
