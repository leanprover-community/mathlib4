/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This files defines the `lint_style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.
-/

open Cli

open System.FilePath

/-- Verifies that every file in the `scripts` directory is documented in `scripts/README.md`. -/
def checkScriptsDocumented : IO Bool := do
  -- Retrieve all scripts (except for the `bench` directory).
  let allScripts ← (walkDir "scripts" fun p ↦ pure (p.components.getD 1 "" != "bench"))
  let allScripts := (allScripts.erase "bench").erase "README.md"
  -- TODO: drop some false positives
  --   nolint.json and noshake.json are data files; as are style-exceptions.txt and nolints-style.txt
  --   these *could* be explicitly allows, or documented as well (perhaps the latter?)
  -- Check if the README text contains each file enclosed in backticks.
  let readme : String ← IO.FS.readFile (System.mkFilePath ["scripts", "README.md"])
  IO.println s!"found {allScripts.size} scripts: {",".intercalate (allScripts.map (·.toString)).toList}"
  -- These are data files for linter exceptions: don't complain about these *for now*.
  let dataFiles := #["nolints.json", "noshake.json", "style-exceptions.txt", "nolints-style.txt"]
  let undocumented := allScripts.filter fun script ↦
    !readme.containsSubstr s!"`{script}`" && !dataFiles.contains script.toString
  if undocumented.size > 0 then
    IO.println s!"error: found {undocumented.size} undocumented scripts:\
      please describe the scripts\n\
      {String.intercalate "," (undocumented.map (·.fileName.get!)).toList}\n\
     in 'scripts/README.md'"
  return undocumented.size > 0

/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let errorStyle := match (args.hasFlag "github", args.hasFlag "update") with
    | (true, _) => ErrorFormat.github
    | (false, true) => ErrorFormat.exceptionsFile
    | (false, false) => ErrorFormat.humanReadable
  let mut numberErrors : UInt32 := 0
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s]) errorStyle
    numberErrors := numberErrors + n
  if ← checkScriptsDocumented then numberErrors := numberErrors + 1
  -- Make sure to return an exit code of at most 125, so this return value can be used further
  -- in shell scripts.
  return min numberErrors 125

/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Print errors solely for the style exceptions file"
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := do lint_style.validate args
