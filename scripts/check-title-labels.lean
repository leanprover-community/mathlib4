/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Mathlib.Tactic.Linter.ValidatePRTitle

/-!
# Checker for well-formed title and labels

This script checks if a PR title matches mathlib's commit conventions,
and if the PR has any contradictory labels.
Not all checks from the commit conventions are implemented: for instance, no effort is made to
verify whether the title or body are written in present imperative tense.
-/

open Cli in
/-- Implementation of the `check-title-labels` command line program.
The exit code is the number of violations found. -/
def checkTitleLabelsCLI (args : Parsed) : IO UInt32 := do
  let title := (args.positionalArg! "title").value
  let labels : Array String := args.variableArgsAs! String
  let mut numberErrors := 0
  if !labels.contains "WIP" then
    -- We do not complain about WIP PRs.
    -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
    let titleErrors := validateTitle title
    numberErrors := numberErrors + titleErrors.size
    for err in titleErrors do
      IO.println err
    -- A feature PR should have a topic label.
    if title.startsWith "feat" && !labels.any
        (fun s ↦ s.startsWith "t-" || ["CI", "IMO"].contains s) then
      IO.println "error: feature PRs should have a 't-something',  'CI' or 'IMO' label"
      numberErrors := numberErrors + 1
  -- Check for contradictory labels.
  if hasContradictoryLabels labels then
    IO.println "error: PR labels are contradictory"
    numberErrors := numberErrors + 1
  return numberErrors


open Cli in
/-- Setting up command line options and help text for `lake exe check-title-labels`. -/
def checkTitleLabels : Cmd := `[Cli|
  «check-title-labels» VIA checkTitleLabelsCLI; ["0.0.1"]
  "Check that a PR title matches the formatting requirements.
  If this PR is a feature PR, also verify that it has a topic label,
  and that there are no contradictory labels."

  ARGS:
    title : String; "this PR's title"
    ...labels : Array String; "list of label names of this PR"
]

/-- The entrypoint to the `lake exe check-title-labels` command. -/
def main (args : List String) : IO UInt32 := checkTitleLabels.validate args
