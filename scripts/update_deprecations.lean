/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Cli.Basic
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
def updateDeprecationsCLI (args : Parsed) : IO UInt32 := do
  -- if you are running `lake exe update_deprecations --tgt filePath`, then `tgt` is `filePath`,
  -- otherwise it is `buildOutput00...0.lean`, where the number of `0` is chosen to avoid clashes
  let verbose := (args.flag? "verbose").isSome
  let tgt := ← match args.flag? "tgt" with
              | some path => return path.as! String
              | none => do
                let mut str :="buildOutput"
                while ← pathExists (addExtension str "lean") do
                  str := str.push '0'
                return (addExtension str "lean").toString
  if verbose then IO.println f!"Using temporary file '{tgt}'\n"
  if ← pathExists tgt then
    IO.println f!"Warning: '{tgt}' exists.\n\n\
    Choose another name by running\n`lake exe update_deprecations <newPath.lean>`"; return 1
  --let mut updates := 0
  -- create the `tgt` file with the output of `lake build`
  buildAndWrite tgt
  let outp := (← IO.Process.run { cmd := "lake", args := #["env", "lean", tgt] }).trimRight
  IO.FS.removeFile tgt
  let ext := String.toNat! <| outp.takeRightWhile (·.isDigit)
  if ext == 0 then
    IO.println "No updates necessary!"
    return 0
  else
    if verbose then IO.println <| outp.dropRightWhile (·.isDigit)
    IO.println f!"{ext}: number of files where some replacement should have taken place"
    -- the exit code is the total number of changes that should have happened, whether or not they
    -- actually took place modulo `UInt32.size = 4294967296` (returning 1 if the remainder is `0`).
    -- In particular, the exit code is `0` if and only if no replacement was necessary.
    return ⟨max 1 (ext % UInt32.size), by unfold UInt32.size; omega⟩

open Cli in
/-- Setting up command line options and help text for `lake exe update_deprecations`. -/
def updateDeprecations : Cmd := `[Cli|
  updateDeprecations VIA updateDeprecationsCLI; ["0.0.1"]
  "Perform the substitutions suggested by the output of `lake build`."

  FLAGS:
    tgt : String; "The temporary file storing the output of `lake exe update_deprecations`.\n\
                  Use as `lake exe update_deprecations --tgt tmpFile.lean`\n\
                  `tmpFile.lean` is optional -- the command uses `buildOutput.lean` by default."
    verbose;      "Produce a verbose output."
]

/-- The entrypoint to the `lake exe update_deprecations` command. -/
def main (args : List String) : IO UInt32 := updateDeprecations.validate args
