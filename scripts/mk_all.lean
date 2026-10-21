/-
Copyright (c) 2024 Yaël Dillies, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Damiano Testa, Thomas R. Murrills
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

namespace Mathlib.Scripts.MkAll

/-- The (persistent) config for a given package. (Not to be confused with the flag values provided
to `mk_all`, which are handled elsewhere.) We may read this from JSON in the future. -/
structure Config where
  /-- Associates `root : Name`s to any extra imports which are not in the
  corresponding directory but which should nonetheless be imported in that root.

  For example, `Mathlib.lean` should also import `Std` and `Batteries`, so we have
  ``{ `Mathlib ↦ #[`Std, `Batteries] }``.

  Note that this uses roots and not libraries, and may refer to "roots" from `extraRootModules`. -/
  extraRootImports : NameMap (Array Name) := {}
  /-- Which libraries of the current package should always be excluded from `mk_all`. -/
  excludedLibs : Array Name := #[]
  /-- Modules (like `Mathlib.Tactic`) which are not roots of any `lean_lib`, but should be treated
  like one. Assumes that the folder they draw their imports from is located at the same path but
  without `.lean`. -/
  extraRootModules : Array Name := #[]

/-- The config used when in mathlib. -/
def mathlibConfig : Config where
  extraRootImports := .ofArray #[(`Mathlib, #[`Std, `Batteries])] Name.quickCmp
  excludedLibs := #[`Cache, `MathlibTest]
  extraRootModules := #[`Mathlib.Tactic]

open Lake in
/-- Small wrapper for getting the lake workspace. -/
def getWorkspace : IO Lake.Workspace := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some ws ← loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "failed to load Lake workspace"
  return ws

/-- Given a `Config`, find the lake `lean_lib`s to process, erroring if the config excludes
libraries that don't exist. -/
def Config.mkAllLibs (cfg : Config) (pkg : Lake.Package) : IO (Array Lake.LeanLib) := do
  let wronglyExcluded := cfg.excludedLibs.filter fun excludedLib =>
    !pkg.leanLibs.any (·.name == excludedLib)
  unless wronglyExcluded.isEmpty do
    throw <| IO.userError s!"Could not find the libraries\
      {String.join <| wronglyExcluded.toList.map (s!"\n  {·.toString (escape := false)}")}\
      \nwhich are excluded by the `mk_all` config among the libraries of the package \
      {pkg.prettyName}. This package contains the libraries:\
      {String.join <| pkg.leanLibs.toList.map (s!"\n  {·.name.toString (escape := false)}")}"
  return pkg.leanLibs.filter (!cfg.excludedLibs.contains ·.name)

/-- The data necessary for updating or creating a root module. -/
structure Root where mkRaw ::
  /-- The name of the (putative) "root" module, e.g. `Mathlib` or `Mathlib.Tactic`. -/
  name : Name
  /-- The `lean_lib` this appears in. We assume `lib.isLocalModule name`. -/
  lib : Lake.LeanLib
  /-- `← IO.FS.realPath lib.srcDir`. We cache this to avoid `IO` and allow comparing the source
  directory of different roots to check for overlaps, after reducing `"."` filename components. -/
  realLibSrcDir : System.FilePath

namespace Root

variable (r : Root)

/-- The directory of modules associated with a root, e.g. `{path}/mathlib4/Mathlib`. -/
def dir : System.FilePath := modToFilePath r.lib.srcDir r.name ""

/-- The module filename associated with a root, e.g. `{path}/mathlib4/Mathlib.lean`. -/
def fileName : System.FilePath := modToFilePath r.lib.srcDir r.name "lean"

/-- We have `r₁.lt r₂` if the root module designated by `r₁` might be included in `r₂`. -/
def lt (r₁ r₂ : Root) : Bool :=
  r₁.realLibSrcDir == r₂.realLibSrcDir && r₁.name != r₂.name && r₂.name.isPrefixOf r₁.name

/-- Construct a `Root`. Also checks that the root is a path. `rootOrigin : String` is used in the
parenthetical `(from {rootOrigin})` to provide better error messages. -/
protected def mk (name : Name) (lib : Lake.LeanLib) (rootOrigin : String) :
    IO Root := do
  let root := { name, lib, realLibSrcDir := ← IO.FS.realPath lib.srcDir : Root }
  unless ← root.dir.isDir do
    throw <| IO.userError s!"Expected the root `{root.name}` (from {rootOrigin}) to be a \
      directory at path:\n  {root.dir}"
  return root

/-- Makes an array of `Root`s for the roots of the given `LeanLib` which have directories. Skips those for which no directory exists. -/
def ofLeanLib (lib : Lake.LeanLib) : IO (Array Root) :=
  lib.roots.filterMapM fun name => do
    let root := { name, lib, realLibSrcDir := ← IO.FS.realPath lib.srcDir : Root }
    if ← root.dir.isDir then return root else return none

end Root

/-- Given a putative (pseudo)root `name`, finds the `Root` associated with it. Errors if it is not
already a directory (but allows it to not be a module). `rootOrigin : String` is used in the
parenthetical `(from {rootOrigin})` to provide better error messages. -/
def findRoot (pkg : Lake.Package) (name : Name) (rootOrigin : String) : IO Root := do
  -- Note that `isLocalModule` doesn't actually check that a module exists, just that the name
  -- *could* be a module built by this library. This includes modules not imported in the root.
  let some lib := pkg.leanLibs.findRev? (·.isLocalModule name)
    | throw <| IO.userError s!"Could not find a `lean_lib` in the package {pkg.prettyName} \
      in which the root `{name}` (from {rootOrigin}) could live.\n\
      This package contains the libraries:\
      {String.join <| pkg.leanLibs.toList.map (s!"\n  {·.name.toString (escape := false)}")}"
  Root.mk name lib (rootOrigin := rootOrigin)

/-- Make the array of roots from the `--lib` flag. -/
def mkOnlyRoots (pkg : Lake.Package) (only : Array String) : IO (Array Root) := do
  let mut roots := #[]
  for root in only do
    if let some lib := pkg.leanLibs.findRev? (root == ·.name.toString (escape := false)) then
      let libRoots ← Root.ofLeanLib lib
      unless libRoots.isEmpty do
        roots := roots ++ (← Root.ofLeanLib lib)
        continue
    -- Fall through to see if this is a module-style root, not a `lean_lib`
    let name := root.toName
    if name.isAnonymous then
      throw <| IO.userError s!"`{root}` (from `--lib`) is neither a valid `lean_lib` nor a \
        valid module name."
    -- Add `only`s that are in libs but are not libs
    roots := roots.push <|← findRoot pkg root.toName (rootOrigin := "`--lib`")
  return roots

/-- Returns the `Root`s to process, with the roots that may be included as imports in future roots
first (e.g. `Mathlib.Tactic` precedes `Mathlib`). -/
def Config.mkAllRoots (cfg : Config) (pkg : Lake.Package)
    (only? : Option (Array String) := none) :
    IO (Array Root) := do
  let roots ← do
    if let some only := only? then
      mkOnlyRoots pkg only
    else
      let libs ← cfg.mkAllLibs pkg
      let mut roots ← libs.flatMapM Root.ofLeanLib
      for name in cfg.extraRootModules do
        roots := roots.push <|← findRoot pkg name
          (rootOrigin := "the `mk_all` config's `extraRootModules")
      pure roots
  return roots.qsort (·.lt ·)

/-- Handles a `Root` and updates the associated file, printing logs to stdout. Returns `true` if it
performed an update and `false` if the resulting file was unchanged. -/
def handleRoot (cfg : Config) (root : Root) (git : Bool) (check : Bool) (forceModule : Bool) :
    IO Bool := do
  let fileName := root.fileName
  -- The existing content and header. This is `none` if the file does not exist.
  let existing? ← if !(← pathExists fileName) then pure none else do
    let existingContent ← IO.FS.readFile fileName
    try
      pure <| some (existingContent, ← Lean.parseImports' existingContent fileName.toString)
    catch e =>
      throw <| IO.userError s!"\
        Could not parse the header of `{root.name}` at {fileName}: {e.toString}\n\
        Fix or delete the file, then re-run `mk_all`\
        {if root.lib.requiresModuleSystem && !root.lib.allowNonModules then "" else
          " (with `--module` if you want a module-style aggregator)"}."
  -- If `--module` was passed explicitly, honor it. If the library requires the module system,
  -- use `module`. Otherwise, if the aggregator file already exists, infer whether it uses the
  -- module system; if not, default to plain.
  let useModule := forceModule || (root.lib.requiresModuleSystem && !root.lib.allowNonModules)
      || existing?.any (·.2.isModule)
  let mut allMods ← getAllModulesSorted git root.dir (srcDir := root.realLibSrcDir)
  -- Prepend extra mods for this root
  if let some extraMods := cfg.extraRootImports.get? root.name then
    allMods := extraMods ++ allMods
  -- Preserve the runtime/elaboration boundary when regenerating an aggregator.
  let metaImports := existing?.map (·.2.imports.filter (·.isMeta) |>.map (·.module)) |>.getD #[]
  let newFileContent := s!"\
    {if useModule then "module  -- shake: keep-all --deprecated_module: ignore\n\n" else ""}\
    {"\n".intercalate <| Array.toList <| allMods.map fun mod => s!"\
      {if useModule then "public " else ""}\
      {if metaImports.contains mod then "meta " else ""}\
      import {mod}"}\
    \n"
  if let some (existingContent, _) := existing? then
    if existingContent != newFileContent then
      if check then
        IO.println s!"The root file `{root.name}` at '{fileName}' is out of date: \
          run `lake exe mk_all{if git then " --git" else ""}` to update it"
      else
        IO.println s!"Updating `{root.name}` at '{fileName}'"
        IO.FS.writeFile fileName newFileContent
    else
      return false -- This is the one case in which we do not need to update
  else
    if check then
      IO.println s!"Root file `{root.name}` does not exist at '{fileName}'"
    else
      IO.println s!"Creating root file `{root.name}` at '{fileName}'"
      IO.FS.writeFile fileName newFileContent
  return true -- All paths here involve updating the file

end MkAll

open IO.FS IO.Process Name Cli MkAll in
/-- Implementation of the `mk_all` command line program.
The exit code is the number of files that the command updates/creates. -/
def mkAllCLI (args : Parsed) : IO UInt32 := do
  -- Check whether the `--git` flag was set
  let git := (args.flag? "git").isSome
  -- Check whether we only verify the files, or update them in-place.
  let check := (args.flag? "check").isSome
  -- If `--module` is passed, force module style; otherwise infer from the existing
  -- aggregator file (when present), or default to plain.
  let forceModule := (args.flag? "module").isSome
  -- Check whether the `--lib` flag was set. If so, process the root files specified.
  -- Else process all the libraries of the package.
  let onlyLibs? := args.flag? "lib" |>.map fun lib => lib.as! (Array String)
  let pkg := (← getWorkspace).root
  -- TODO: read config from json
  let cfg := if pkg.origName == `mathlib then mathlibConfig else {}
  let roots ← cfg.mkAllRoots pkg (only? := onlyLibs?)
  let mut numUpdates : UInt32 := 0
  for root in roots do
    if ← handleRoot cfg root git check forceModule then
      numUpdates := numUpdates + 1
  if numUpdates == 0 then
    IO.println "No update necessary"
  -- Make sure to return an exit code of at most 125, so this return value can be used further
  -- in shell scripts.
  return min numUpdates 125

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
    lib : Array String;
            "Create or update a module importing all Lean files from the specified \
             library or subfolder(s). Multiple libraries may be provided and separated by commas. \
             Module-style names of directories that are not actual `lean_libs` may also be used \
             (e.g. `Mathlib.Tactic`)."
    git;    "Use the folder content information from git."
    check;  "Only check if the files are up-to-date; print an error if not"
    module; "Force the aggregator file to be generated as a `module` with `public` imports. \
             When this flag is omitted, a `module` is used if the library of the associated file \
             requires the module system or the existing file is already a module. Otherwise, this \
             defaults to a non-module import."
]

end Mathlib.Scripts

/-- The entrypoint to the `lake exe mk_all` command. -/
def main (args : List String) : IO UInt32 := Mathlib.Scripts.mkAll.validate args
