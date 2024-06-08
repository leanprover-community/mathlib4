/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic

open Lean Elab

open Cli in
/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  return 0

open Cli in
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
    regenerate; "(not implemented yet) Regenerate the file of style exceptions: \
                 add entries for all current errors and update or remove all obsolete ones"

  ARGS:
    ...files : String; "Only lint these file(s)"
]

/-- The entry point to the `lake exe lint_style` command. -/
def main (args : List String) : IO UInt32 := return 0
