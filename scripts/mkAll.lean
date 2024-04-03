/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa
-/
import Cli.Basic
import Lean.Util.Path

/-!
# Script to create a file importing all files from a folder

This file declares a command to gather all Lean files from a folder into a single Lean file.
-/

/-- the command `git ls-files '*.lean'` -/
def gitLSFiles : IO.Process.SpawnArgs where
  cmd := "git"
  args := #["ls-files", "*.lean"]

open Lean System.FilePath

/-- `getAll git str` takes all `.lean` files in the dir `str` (recursing into sub-dirs) and
returns the string
```
import file₁
...
import fileₙ
```
The input `git` is a `Bool`ean flag:
* `true` means that the command uses `git ls-files` to find the relevant files;
* `false` means that the command recursively scans all dirs searching for `.lean` files.
-/
def getAll (git : Bool) (ml : String) : IO String := do
  let ml.lean := addExtension ⟨ml⟩ "lean"  -- `Mathlib.lean`
  let stdout : List System.FilePath ← (do
    if git then
      let mlDir := ml.push pathSeparator   -- `Mathlib/`
      let allLean ← IO.Process.run gitLSFiles
      return ((allLean.splitOn "\n").filter mlDir.isPrefixOf).map (⟨·⟩)
    else do
      let all := (← System.FilePath.walkDir ml)
      return ((all.filter (·.extension == some "lean")).qsort (·.toString < ·.toString)).toList)
  let files := (stdout.erase ml.lean).toArray.qsort (·.toString < ·.toString)
  let withImport ← files.mapM fun f => return "import " ++ (← moduleNameOfFileName f none).toString
  return ("\n".intercalate withImport.toList).push '\n'

open IO.FS IO.Process Name Cli in
/-- Implementation of the `mk_all` command line program. -/
def mkAllCLI (args : Parsed) : IO UInt32 := do
  -- Check whether the `--git` flag was set
  let git := match args.flag? "git" with
  | some _ => true
  | none => false
  -- Check whether the `--lib` flag was set. If so, build the file corresponding to the library
  -- passed to `--lib`. Else build the standard mathlib libraries.
  let libs := match args.flag? "lib" with
  | some lib => #[lib.as! String]
  | none => #["Mathlib", "MathlibExtras", "Mathlib/Tactic", "Counterexamples", "Archive"]
  for d in libs do
    let fileName := addExtension d "lean"
    let fileContent ← getAll git d
    if (← IO.FS.readFile fileName) != fileContent then
      IO.println s!"Updating '{fileName}'"
      IO.FS.writeFile fileName fileContent
  return 0

open Cli in
/-- Setting up command line options and help text for `lake exe mkAll`. -/
def mkAll : Cmd := `[Cli|
  mkAll VIA mkAllCLI; ["0.0.1"]
  "Generate a file importing all the files of a Lean folder. \
   By default, it generates the files for the folders `Mathlib`, \
   `MathlibExtras`, `Mathlib/Tactic`, `Counterexamples`, `Archive`. \
   If you are working in a downstream project, use `lake exe mkAll --lib MyProject`."

  FLAGS:
    lib : String; "Create a folder importing all Lean files from the specified library/subfolder."
    git;          "Use the folder content information from git."
]

/-- The entrypoint to the `lake exe mkAll` command. -/
def main (args : List String) : IO UInt32 := mkAll.validate args
