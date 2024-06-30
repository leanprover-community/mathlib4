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
  -- FIXME: consolidate this validation logic, by incorporating it into the match below
  let update := args.hasFlag "update"
  let regenerate := args.hasFlag "regenerate"
  let fix := args.hasFlag "fix"
  if update && regenerate then
    IO.println "invalid options: the --update and --regenerate flags are mutually exclusive"
    return 2
  else if update && fix then
    IO.println "invalid options: the --update and --fix flags are mutually exclusive"
  else if regenerate && fix then
    IO.println "invalid options: the --regenerate and --fix flags are mutually exclusive"
  let errorStyle := if args.hasFlag "github" then ErrorFormat.github else ErrorFormat.humanReadable
  let mode : OutputSetting := match (update, regenerate, fix) with
  | (true, _, _) => OutputSetting.append
  | (false, true, _) => OutputSetting.regenerate
  | (false, false, true) => OutputSetting.fix
  | (false, false, false) => OutputSetting.print errorStyle
  if !(mode matches OutputSetting.print _) && args.hasFlag "github" then
    IO.println "warning: the --github option has no effect when updating the style exceptions file"
    return 2
  let mut numberErrorFiles : UInt32 := 0

  -- When regenerating the exceptions, we have to be careful to not over-write one collection
  -- of errors in the first turn: down-grade all but the first output setting to `append`.
  numberErrorFiles ← lintAllFiles (System.mkFilePath ["Mathlib.lean"]) mode
  let mode' := if mode == OutputSetting.regenerate then OutputSetting.append else mode
  for s in ["Archive.lean", "Counterexamples.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s]) mode'
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
                 otherwise, produce human-readable output\n\
                 has no effect when updating the style exceptions file"
    update;     "Append all new errors to the current list of exceptions \
                 (leaving existing entries untouched)"
    regenerate; "Regenerate the file of style exceptions: \
                 add entries for all current errors and update or remove all obsolete ones"
    fix;        "Where possible, fix style errors by rewriting the affected lines in-place"
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := do lint_style.validate args
