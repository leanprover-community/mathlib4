/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Mathlib.Tactic.Linter.ValidatePRTitle

/-!
# Checker for well-formed title and labels

This script checks if a PR title matches some of mathlib's commit conventions.
Currently, we only verify very basic checks: this could be made stricter in the future.

-/

open Cli in
/-- Implementation of the `check-title-labels` command line program.
The exit code is the number of violations found. -/
def checkTitleLabelsCLI (args : Parsed) : IO UInt32 := do
  let title := (args.positionalArg! "title").value
  let labels : Array String := args.variableArgsAs! String
  -- We not validate titles of WIP PRs.
  if labels.contains "WIP" then return 0

  let mut numberErrors := 0
  -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
  let titleErrors : Array String := validateTitle title
  numberErrors := UInt32.ofNat titleErrors.size
  for err in titleErrors do
    IO.println err
  return min numberErrors 125

open Cli in
/-- Setting up command line options and help text for `lake exe check-title-labels`. -/
def checkTitleLabels : Cmd := `[Cli|
  «check-title-labels» VIA checkTitleLabelsCLI; ["0.0.1"]
  "Check that a PR title matches the formatting requirements.
  If this PR is a feature PR, also verify that it has a topic label,
  and that there are no contradictory labels."

  FLAGS:
    "labels" : Array String; "list of label names of this PR\
      These are optional; we merely use a WIP label to skip any checks of the PR title"

  ARGS:
    title : String; "this PR's title"

]

/-- The entrypoint to the `lake exe check-title-labels` command. -/
def main (args : List String) : IO UInt32 := checkTitleLabels.validate args
