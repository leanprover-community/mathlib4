/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa
-/
import Cli.Basic
import Lake.CLI.Main
import Mathlib.Util.GetAllModules

/-!
# Script to create a file importing all files from a folder

This file declares a command to gather all Lean files from a folder into a single Lean file.

-/

open Lean System.FilePath

open Lake in
/-- `getLeanLibs` returns the names (as an `Array` of `String`s) of all the libraries
on which the current project depends.
If the current project is `mathlib`, then it excludes the libraries `Cache` and `LongestPole` and
it includes `Mathlib/Tactic`. -/
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
  -- Check whether we only verify the files, or update them in-place.
  let check := (args.flag? "check").isSome
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
    let allFiles ← getAllModulesSorted git d
    let fileContent := ("\n".intercalate (allFiles.map ("import " ++ ·)).toList).push '\n'
    if !(← pathExists fileName) then
      if check then
        IO.println s!"File '{fileName}' does not exist"
      else
        IO.println s!"Creating '{fileName}'"
        IO.FS.writeFile fileName fileContent
      updates := updates + 1
    else if (← IO.FS.readFile fileName) != fileContent then
      if check then
        IO.println s!"The file '{fileName}' is out of date: run `lake exe mk_all{if git then " --git" else ""}` to update it"
      else
        IO.println s!"Updating '{fileName}'"
        IO.FS.writeFile fileName fileContent
      updates := updates + 1
  if updates == 0 then
    IO.println "No update necessary"
  -- Make sure to return an exit code of at most 125, so this return value can be used further
  -- in shell scripts.
  return min updates 125

open Cli in
/-- Setting up command line options and help text for `lake exe mk_all`. -/
def mkAll : Cmd := `[Cli|
  mk_all VIA mkAllCLI; ["0.0.1"]
  "Generate a file importing all the files of a Lean folder. \
   By default, it generates the files for the Lean libraries of the package.\
   In the case of `Mathlib`, it removes the libraries `Cache` and `LongestPole`\
   and it adds `Mathlib/Tactic`. \
   If you are working in a project downstream of mathlib, use `lake exe mk_all --lib MyProject`."

  FLAGS:
    lib : String; "Create a folder importing all Lean files from the specified library/subfolder."
    git;          "Use the folder content information from git."
    check;        "Only check if the files are up-to-date; print an error if not"
]

/-- The entrypoint to the `lake exe mk_all` command. -/
def main (args : List String) : IO UInt32 := mkAll.validate args
