/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Tactic.Linter.TextBased
import Cli.Basic

/-!
# Text-based style linters

This files defines the `lint-style` executable which runs all text-based style linters.
The linters themselves are defined in `Mathlib.Tactic.Linter.TextBased`.
-/

open Cli Mathlib.Linter.TextBased

/-- Implementation of the `lint-style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let mode : OutputSetting := match (args.hasFlag "update", args.hasFlag "github") with
    | (true, _) => OutputSetting.update
    | (false, true) => OutputSetting.print ErrorFormat.github
    | (false, false) => OutputSetting.print ErrorFormat.humanReadable
  -- Read all module names to lint.
  let mut allModules := #[]
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    allModules := allModules.append ((← IO.FS.lines s).map (·.stripPrefix "import "))
  -- note: since we manually add "Batteries" to "Mathlib.lean", we remove it here manually
  allModules := allModules.erase "Batteries"
  let numberErrorFiles ← lintModules allModules mode (args.hasFlag "fix")
  -- If run with the `--update` or `--fix` argument, return a zero exit code.
  -- Otherwise, make sure to return an exit code of at most 125,
  -- so this return value can be used further in shell scripts.
  if args.hasFlag "update" || args.hasFlag "fix" then
    return 0
  else return min numberErrorFiles 125

/-- Setting up command line options and help text for `lake exe lint-style`. -/
-- so far, no help options or so: perhaps that is fine?
def lintStyle : Cmd := `[Cli|
  «lint-style» VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Also update the style exceptions file.\
      This adds entries for any new exceptions, removes any entries which are no longer necessary,\
      and tries to not modify exception entries unless necessary.
      To fully regenerate the list of style exceptions, delete `style-exceptions.txt`
      and run this script again with this flag."
    fix;        "Automatically fix the style error, if possible"
]

/-- The entry point to the `lake exe lint-style` command. -/
def main (args : List String) : IO UInt32 := do lintStyle.validate args
