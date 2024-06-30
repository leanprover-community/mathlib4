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
  if args.hasFlag "update" && args.hasFlag "regenerate" then
    IO.println "invalid options: the --update and --regenerate flags are mutually exclusive"
    return 2
  let errorStyle := if args.hasFlag "github" then ErrorFormat.github else ErrorFormat.humanReadable
  let mode : OutputSetting := match (args.hasFlag "update", args.hasFlag "regenerate") with
  | (true, _) => OutputSetting.append
  | (_, true) => OutputSetting.regenerate
  | _ => OutputSetting.print errorStyle
  let mut numberErrorFiles : UInt32 := 0
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s]) mode
    numberErrorFiles := numberErrorFiles + n
  return numberErrorFiles

/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Mathlib/, Archive/ and Counterexamples/.
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Append all new errors to the current list of exceptions \
                 (leaving existing entries untouched)"
    regenerate; "Regenerate the file of style exceptions: \
                 add entries for all current errors and update or remove all obsolete ones"
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := do lint_style.validate args
