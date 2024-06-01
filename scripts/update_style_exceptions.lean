/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Util.GetAllModules

/-!
# Style exception file generator

This script completely regenerates the `scripts/style-exceptions.txt` file.
Typically this should only be run by automation. Human contributors shouldn't need to run this
unless they are making changes to the linting script.
-/

/-- The entry point to the `lake exe update_style_exceptions` command.
Regenerate the `scripts/style-exceptions.txt` file. -/
def main : IO UInt32 := do
  -- Find all files in the mathlib, archive and counterexamples directories.
  let mut allFiles ← getAllFiles false "Mathlib"
  let archive ← getAllFiles false "Archive"
  let cex ← getAllFiles false "Counterexamples"
  allFiles := (allFiles.append archive).append cex
  -- Run the linter on all of them; gather the resulting exceptions and sort them.
  -- Call xargs, to avoid spawning a new python process for each file.
  -- `IO.Process.output` passes empty standard input, so this actually works.
  -- `-s` specifies the maximum size of the command line (including the initial argument):
  -- since we pass all input files as initial arguments to xargs, this small hack is necessary.
  -- As of May 2024, the limit 200 000 suffices; therefore, we pass 300 000 to be future-proof.
  let args := #["-s", "300000", "./scripts/lint-style.py"].append
    (allFiles.map System.FilePath.toString)
  let out ← IO.Process.output { cmd := "xargs", args := args }
  if out.exitCode != 0 then
    println! "error {out.exitCode} on updating style exceptions : {out.stderr}"
    return out.exitCode
  let lines := out.stdout.splitOn "\n"
  let final := "\n".intercalate (lines.toArray.qsort (· < ·)).toList
  IO.FS.writeFile (System.mkFilePath ["scripts", "style-exceptions.txt"]) final
  return 0
