/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa
-/
import Cli.Basic
import Lean.Util.Path
import Lake.CLI.Main

/-!
# Script to create a file importing all files from a folder

This file declares a command to gather all Lean files from a folder into a single Lean file.
-/

open Lean System.FilePath

/-- `getAll git ml` takes all `.lean` files in the dir `ml` (recursing into sub-dirs) and
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
  let stdout : Array System.FilePath ← (do
    if git then
      let mlDir := ml.push pathSeparator   -- `Mathlib/`
      let allLean ← IO.Process.run { cmd := "git", args := #["ls-files", mlDir ++ "*.lean"] }
      return (((allLean.dropRightWhile (· == '\n')).splitOn "\n").map (⟨·⟩)).toArray
    else do
      let all ← walkDir ml
      return all.filter (·.extension == some "lean"))
  let files := (stdout.erase ml.lean).qsort (·.toString < ·.toString)
  let withImport ← files.mapM fun f => do
    if ← pathExists f then
      return "import " ++ (← moduleNameOfFileName f none).toString
    else return ""
  return ("\n".intercalate (withImport.filter (· != "")).toList).push '\n'

open Lake in
/-- `getLeanLibs` returns the array of names (as an `Array` of `String`s) of all the libraries
on which the current project depends.
If the package is `mathlib`, then it excludes the libraries `Cache` and `LongestPole` and it
includes `Mathlib/Tactic`. -/
def getLeanLibs : IO (Array String) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let ws ← MonadError.runEIO (MainM.runLogIO (loadWorkspace config)).toEIO
  let package := ws.root
  let libs := (package.leanLibs.map (·.name)).map (·.toString)
  return if package.name == `mathlib then
    libs.erase "Cache" |>.erase "LongestPole" |>.push ("Mathlib".push pathSeparator ++ "Tactic")
  else
    libs

open IO.FS IO.Process Name Cli in
/-- Implementation of the `mk_all` command line program.
The exit code is the number of files that the command updates/creates. -/
def mkAllCLI (args : Parsed) : IO UInt32 := do
  -- Check whether the `--git` flag was set
  let git := (args.flag? "git").isSome
  -- Check whether the `--lib` flag was set. If so, build the file corresponding to the library
  -- passed to `--lib`. Else build all the libraries of the package.
  -- If the package is `mathlib`, then it removes the libraries `Cache` and `LongestPole` and it
  -- adds `Mathlib/Tactic`.
  let libs := ← match args.flag? "lib" with
              | some lib => return #[lib.as! String]
              | none => getLeanLibs
  let mut updates := 0
  for d in libs.reverse do  -- reverse to create `Mathlib/Tactic.lean` before `Mathlib.lean`
    let fileName := addExtension d "lean"
    let fileContent ← getAll git d
    if !(← pathExists fileName) then
      IO.println s!"Creating '{fileName}'"
      updates := updates + 1
      IO.FS.writeFile fileName fileContent
    else if (← IO.FS.readFile fileName) != fileContent then
      IO.println s!"Updating '{fileName}'"
      updates := updates + 1
      IO.FS.writeFile fileName fileContent
  if updates == 0 then
    IO.println "No update necessary"
  return updates

open Cli in
/-- Setting up command line options and help text for `lake exe mk_all`. -/
def mkAll : Cmd := `[Cli|
  mk_all VIA mkAllCLI; ["0.0.1"]
  "Generate a file importing all the files of a Lean folder. \
   By default, it generates the files for the Lean libraries of the package.\
   In the case of `Mathlib`, it removes the libraries `Cache` and `LongestPole`\
   and it adds `Mathlib/Tactic`. \
   If you are working in a downstream project, use `lake exe mk_all --lib MyProject`."

  FLAGS:
    lib : String; "Create a folder importing all Lean files from the specified library/subfolder."
    git;          "Use the folder content information from git."
]

/-- The entrypoint to the `lake exe mk_all` command. -/
def main (args : List String) : IO UInt32 := mkAll.validate args
