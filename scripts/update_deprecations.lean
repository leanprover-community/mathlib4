/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Cli.Basic
import Lean.Elab.Frontend
import Mathlib.Tactic.UpdateDeprecations

/-!
# Script to automatically update deprecated declarations

Running `lake exe update_deprecations` assumes that there is a working cache and
uses the information from deprecations to automatically substitute deprecated declarations.

Currently, this only works with non-namespaced ones, but this will be fixed once the deprecation
warning for dot-notation becomes available.
-/

open Lean System.FilePath

open IO.FS IO.Process Name Cli in
/-- Implementation of the `update_deprecations` command line program.
The exit code is the number of files that the command updates/creates. -/
def updateDeprecationsCLI (_args : Parsed) : IO UInt32 := do
  let buildOutput ← getBuild
  if buildOutput.isEmpty then return 1
  Lean.initSearchPath (← Lean.findSysroot)
  -- create the environment with `import Mathlib.Tactic.UpdateDeprecations`
  let env : Environment ← importModules #[{module := `Mathlib.Tactic.UpdateDeprecations}] {}
  -- process the `lake build` output, catching messages
  let (_, msgLog) ← Lean.Elab.process buildOutput env {}
  let exitCode := ← match msgLog.msgs.toArray with
    | #[msg, exCode] => do
      IO.println f!"{(← msg.toString).trimRight}"
      return String.toNat! (← exCode.toString).trimRight
    | msgs => do
      IO.println f!"{← msgs.mapM (·.toString)}"
      return 1
  if exitCode == 0 then return 0
  -- the exit code is the total number of changes that should have happened, whether or not they
  -- actually took place modulo `UInt32.size = 4294967296` (returning 1 if the remainder is `0`).
  -- In particular, the exit code is `0` if and only if no replacement was necessary.
  else return ⟨max 1 (exitCode % UInt32.size), by unfold UInt32.size; omega⟩

open Cli in
/-- Setting up command line options and help text for `lake exe update_deprecations`. -/
def updateDeprecations : Cmd := `[Cli|
  updateDeprecations VIA updateDeprecationsCLI; ["0.0.1"]
  "Perform the substitutions suggested by the output of `lake build`."

  FLAGS:
    --verbose : String;      "Produce a verbose output."
]

/-- The entrypoint to the `lake exe update_deprecations` command. -/
def main (args : List String) : IO UInt32 := updateDeprecations.validate args
