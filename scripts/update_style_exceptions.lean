/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Cli.Basic
import Lean.Util.Path
import Lake.CLI.Main

/-!
# Style exception file generator

This script completely regenerates the `scripts/style-exceptions.txt` file.
Typically this should only be run by automation. Human contributors shouldn't need to run this unless they are making changes to the linting script.

-/

open Lean System.FilePath

-- XXX: this is extracted from the `mk_all` script.
-- can I put this in a common place, to make it re-usable?
/-- `getAll' git d` takes all `.lean` files in the directory `d`
(recursing into sub-directories) and returns the array of file names `#[file₁, ..., fileₙ]`.

The input `git` is a `Bool`ean flag:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files.
-/
def getAll'' (git : Bool) (ml : String) : IO (Array String) := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  -- for example, `Mathlib.lean`
  let allModules : Array System.FilePath ← (do
    if git then
      let mlDir := ml.push pathSeparator   -- for example, `Mathlib/`
      let allLean ← IO.Process.run { cmd := "git", args := #["ls-files", mlDir ++ "*.lean"] }
      return (((allLean.dropRightWhile (· == '\n')).splitOn "\n").map (⟨·⟩)).toArray
    else do
      let all ← walkDir ml
      return all.filter (·.extension == some "lean"))
  let files := (allModules.erase ml.lean).qsort (·.toString < ·.toString)
  let filtered ← files.mapM fun f => do
    -- this check is helpful in case the `git` option is on and a local file has been removed
    if ← pathExists f then
      return f.toString
    else return ""
  return filtered.filter (· != "")


def generate_style_exceptions : IO String := do
  -- Find all files in the mathlib directory.
  let mut all_files ← getAll'' true "Mathlib"
  -- Since we can, also extend this to the Archive and Counterexamples.
  let archive ← getAll'' true "Archive"
  let cex ← getAll'' true "Counterexamples"
  all_files := (all_files.append archive).append cex
  -- Run the linter on all of them; gather the resulting exceptions and sort them.
  -- XXX: can this be done in a more functional style? like
  -- let output := all_files.map (fun file ↦ IO.Process.run { cmd := "python3", args := #[file] }),
  -- but running the IO in each step?
  let mut output : Array String := Array.mkEmpty 0
  let mut i := 0
  for file in all_files do
    i := i + 1
    -- needs about 3s for 100 files; `update_style_exceptions.sh` take 0.6s overall!
    if i == 100 then break
    -- TODO: can I avoid the process spawning, and call `xargs` instead?
    let out ← IO.Process.run { cmd := "python3", args := #["scripts/lint-style.py", file] }
    output := output.push out
  let sorted_output := (output.filter (fun o ↦ o != "")).qsort (· < ·)
  return "\n".intercalate sorted_output.toList

/-- Implementation of the `update_style_exceptions` command line program. -/
def updateStyleExceptionsCLI (_args : Cli.Parsed) : IO UInt32 := do
  let output ← generate_style_exceptions
  -- IO.println s!"full output was: {output}"
  IO.FS.writeFile (System.mkFilePath ["scripts", "style-exceptions.txt"]) output
  -- TODO: forward errors of the underlying script, somehow!
  return 0

open Cli in
/-- Setting up command line options and help text for `lake exe update_style_exceptions`. -/
-- so far, no help options or so: perhaps that is fine?
def update_style_exceptions : Cmd := `[Cli|
  update_style_exceptions VIA updateStyleExceptionsCLI; ["0.0.1"]
  "Update all style exceptions, TODO complete this docstring."
]

/-- The entry point to the `lake exe update_style_exceptions` command. -/
def main (args : List String) : IO UInt32 := update_style_exceptions.validate args
