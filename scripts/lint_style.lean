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

/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let errorStyle := if args.hasFlag "github" then ErrorFormat.github else ErrorFormat.humanReadable
  let mode : OutputSetting := if args.hasFlag "update" then OutputSetting.update else
    OutputSetting.print errorStyle
  let mut numberErrorFiles : UInt32 := 0
  -- Collect all the modules to read.
  let mut allModules := #[]
  for s in ["Mathlib.lean", "Archive.lean", "Counterexamples.lean"] do
    allModules := allModules.append ((← IO.FS.lines s).map (·.stripPrefix "import "))
  numberErrorFiles ← lintModules allModules mode
  -- Make sure to return an exit code of at most 125, so this return value can be used further
  -- in shell scripts.
  return min numberErrorFiles 125

/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Also update the style exceptions file.\
      This adds entries for any new exceptions, removes any entries which are no longer necessary,\
      and tries to not modify exception entries unless necessary.
      To fully regenerate the list of style exceptions, delete `style-exceptions.txt`
      and again with this flag."
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := do lint_style.validate args
