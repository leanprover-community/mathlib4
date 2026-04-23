/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa
-/
import Cli.Basic
import Lake.CLI.Main
import Mathlib.Util.GetAllModules

-- The `style.header` linter flags `import Lake.CLI.Main` as a potential performance issue.
set_option linter.style.header false
/-!
# Script to create a file importing all files from a folder

This file declares a command to gather all Lean files from a folder into a single Lean file.

-/

open Lean System.FilePath

open Lake in
/-- `getLeanLibs` returns the names (as an `Array` of `String`s) of all the libraries
on which the current project depends.
If the current project is `mathlib`, then it excludes the libraries `Cache` and `MathlibTest` and
it includes `Mathlib/Tactic`. -/
def getLeanLibs : IO (Array String) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some ws ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  let package := ws.root
  let libs := (package.leanLibs.map (·.name)).map (·.toString)
  return if package.baseName == `mathlib then
    libs.erase "Cache" |>.erase "MathlibTest"
      |>.push ("Mathlib".push pathSeparator ++ "Tactic")
  else
    libs

/-- Skip leading ASCII whitespace and Lean comments (line `-- ...` and nested `/- ... -/` block
comments) from the start of `s`, returning the remaining slice. -/
partial def skipWsAndComments (s : String.Slice) : String.Slice := Id.run do
  let s := s.trimAsciiStart
  if s.startsWith "--" then
    let mut t := s.drop 2
    while !t.isEmpty && t.front != '\n' do
      t := t.drop 1
    return skipWsAndComments t
  if s.startsWith "/-" then
    let mut t := s.drop 2
    let mut depth := 1
    while depth > 0 && !t.isEmpty do
      if t.startsWith "/-" then
        depth := depth + 1
        t := t.drop 2
      else if t.startsWith "-/" then
        depth := depth - 1
        t := t.drop 2
      else
        t := t.drop 1
    return skipWsAndComments t
  return s

/-- Decide whether the given aggregator-file contents use the module system,
by checking if the first non-comment, non-whitespace token is the `module` keyword. -/
def usesModuleSystem (content : String) : Bool :=
  -- Strip an optional UTF-8 BOM before scanning.
  let bom := (Char.ofNat 0xfeff).toString
  let content := if content.startsWith bom then content.drop bom.length else content.toSlice
  let rest := skipWsAndComments content
  if rest.startsWith "module" then
    let after := rest.drop "module".length
    after.isEmpty || !(after.front.isAlphanum || after.front == '_')
  else
    false

open IO.FS IO.Process Name Cli in
/-- Implementation of the `mk_all` command line program.
The exit code is the number of files that the command updates/creates. -/
def mkAllCLI (args : Parsed) : IO UInt32 := do
  -- Check whether the `--git` flag was set
  let git := (args.flag? "git").isSome
  -- Check whether we only verify the files, or update them in-place.
  let check := (args.flag? "check").isSome
  -- The `--module` flag only affects newly created aggregator files; for existing files,
  -- module-ness is inferred from the first non-comment, non-whitespace token.
  let moduleFlag := (args.flag? "module").isSome
  -- Check whether the `--lib` flag was set. If so, build the file corresponding to the library
  -- passed to `--lib`. Else build all the libraries of the package.
  -- If the package is `mathlib`, then it removes the libraries `Cache` and `MathlibTest` and it
  -- adds `Mathlib/Tactic`.
  let libs := ← match args.flag? "lib" with
              | some lib => return #[lib.as! String]
              | none => getLeanLibs
  let mut updates := 0
  for d in libs.reverse do  -- reverse to create `Mathlib/Tactic.lean` before `Mathlib.lean`
    let fileName := addExtension d "lean"
    let fileExists ← pathExists fileName
    let existingContent ← if fileExists then IO.FS.readFile fileName else pure ""
    -- If the aggregator file already exists, infer whether it uses the module system;
    -- otherwise, fall back to the `--module` flag.
    let useModule := if fileExists then usesModuleSystem existingContent else moduleFlag
    let mut allFiles ← getAllModulesSorted git d
    -- mathlib exception: manually import Std and Batteries in `Mathlib.lean`
    if d == "Mathlib" then
      allFiles := #["Std", "Batteries"] ++ allFiles
    let fileContent := (if useModule then "module  -- shake: keep-all\n\n" else "") ++
      ("\n".intercalate (allFiles.map ((if useModule then "public " else "") ++ "import " ++ ·)).toList) ++
      (if d == "Mathlib" then "\n\nset_option linter.style.longLine false" else "") ++
      "\n"
    if !fileExists then
      if check then
        IO.println s!"File '{fileName}' does not exist"
      else
        IO.println s!"Creating '{fileName}'"
        IO.FS.writeFile fileName fileContent
      updates := updates + 1
    else if existingContent != fileContent then
      if check then
        IO.println s!"The file '{fileName}' is out of date: \
          run `lake exe mk_all{if git then " --git" else ""}` to update it"
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
   By default, it generates the files for the Lean libraries of the package. \
   In the case of `Mathlib`, it removes the libraries `Cache` and `MathlibTest` \
   and it adds `Mathlib/Tactic`. \
   If you are working in a project downstream of mathlib, use `lake exe mk_all --lib MyProject`."

  FLAGS:
    lib : String; "Create a folder importing all Lean files from the specified library/subfolder."
    git;          "Use the folder content information from git."
    check;        "Only check if the files are up-to-date; print an error if not"
    module;       "When creating a new aggregator file, generate it as a `module` with \
                   `public` imports. Existing files keep their current style (module or plain), \
                   inferred from their first non-comment, non-whitespace token."
]

/-- The entrypoint to the `lake exe mk_all` command. -/
def main (args : List String) : IO UInt32 := mkAll.validate args
