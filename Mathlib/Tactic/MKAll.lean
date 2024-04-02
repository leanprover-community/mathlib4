/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Lean.Elab.Command

/-!
#  An implementation of the `mk_all.sh` script in Lean
-/

namespace Mathlib.MKAll

/-- the command `git ls-files '*.lean'` -/
def gitLSFiles : IO.Process.SpawnArgs where
  cmd := "git"
  args := #["ls-files", "*.lean"]

open Lean System.FilePath

/-- `getAll git? str` takes all `.lean` files in the dir `str` (recursing into sub-dirs) and
returns the string
```
import file₁
...
import fileₙ
```
The input `git?` is a `Bool`ean flag:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files. -/
def getAll (git? : Bool) (ml : String) : IO String := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  -- `Mathlib.lean`
  let stdout : List System.FilePath ← (do
    if git? then
      let mlDir := ml.push pathSeparator   -- `Mathlib/`
      let allLean ← IO.Process.run gitLSFiles
      return ((allLean.splitOn "\n").filter mlDir.isPrefixOf).map (⟨·⟩)
    else do
      let all := (← System.FilePath.walkDir ml)
      return ((all.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)).toList)
  let files := (stdout.erase ml.lean).toArray.qsort (·.toString < ·.toString)
  let withImport ← files.mapM fun f => return "import " ++ (← moduleNameOfFileName f none).toString
  return ("\n".intercalate withImport.toList).push '\n'

/-- the "Mathlib usual suspects" for "import all" files. -/
abbrev candidates := #["Mathlib", "MathlibExtras", "Mathlib/Tactic", "Counterexamples", "Archive"]

/-- Using `run_cmd mkAll git? arr` creates an "import all" file for each of the entries in the
array `arr`.
The `git?` input is a `Bool`ean:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files.
-/
def mkAll (git? : Bool) (cands : Array String) : IO Unit := do
  for d in cands do
    let fileName := addExtension d "lean"
    let fileContent ← getAll git? d
    if (← IO.FS.readFile fileName) != fileContent then
      IO.println s!"Updating '{fileName}'"
      IO.FS.writeFile fileName fileContent

/-!
By default, we call `mkAll` with
* `git?` set to `true` -- we use `git ls-files`;
* `arr` set to `candidates` -- we create the "Mathlib usual suspects" for "import all" files.
-/
run_cmd mkAll (git? := true) (cands := candidates)
