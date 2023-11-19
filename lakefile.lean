import Lake

open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false",
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

-- These are additional settings which do not affect the lake hash,
-- so they can be enabled in CI and disabled locally or vice versa.
-- Warning: Do not put any options here that actually change the olean files,
-- or inconsistent behavior may result
def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package mathlib where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs

/-- `lake exe checkYaml` verifies that all declarations referred to in `docs/*.yaml` files exist. -/
lean_exe checkYaml where
  root := `scripts.checkYaml
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/leanprover-community/quote4" @ "master"
require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
require Cli from git "https://github.com/leanprover/lean4-cli" @ "main"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.22"

lean_lib Cache where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Cache]

/-- `lake exe cache get` retrieves precompiled `.olean` files from a central server. -/
lean_exe cache where
  root := `Cache.Main

/--
When a package depending on Mathlib updates its dependencies,
update its toolchain to match Mathlib's and fetch the new cache.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  if rootPkg.name = pkg.name then
    return -- do not run in Mathlib itself
  /-
  Once Lake updates the toolchains,
  this toolchain copy will be unnecessary.
  https://github.com/leanprover/lean4/issues/2752
  -/
  let wsToolchainFile := rootPkg.dir / "lean-toolchain"
  let mathlibToolchain := ← IO.FS.readFile <| pkg.dir / "lean-toolchain"
  IO.FS.writeFile wsToolchainFile mathlibToolchain
  if (← IO.getEnv "MATHLIB_NO_CACHE_ON_UPDATE") != some "1" then
    /-
    Instead of building and running cache via the Lake API,
    spawn a new `lake` since the toolchain may have changed.
    -/
    let exitCode ← IO.Process.spawn {
      cmd := "elan"
      args := #["run", mathlibToolchain.trim, "lake", "exe", "cache", "get"]
    } >>= (·.wait)
    if exitCode ≠ 0 then
      logError s!"{pkg.name}: failed to fetch cache"

lean_lib MathlibExtras where
  roots := #[`MathlibExtras]

lean_lib Archive where
  roots := #[`Archive]

lean_lib Counterexamples where
  roots := #[`Counterexamples]

lean_lib ImportGraph where
  roots := #[`ImportGraph]

/-- `lake exe graph` constructs import graphs in `.dot` or graphical formats. -/
lean_exe graph where
  root := `ImportGraph.Main
  supportInterpreter := true

/-- Additional documentation in the form of modules that only contain module docstrings. -/
lean_lib docs where
  roots := #[`docs]


section Scripts

open System

partial def moduleNamesIn (dir : FilePath)
    (ext := "lean") (includeDirs? := false) : IO (Array Name) :=
  dir.readDir >>= Array.concatMapM fun entry ↦ do
    if (← entry.path.isDir) then
      let n := entry.fileName.toName
      let mods ← .map (n ++ ·) <$> moduleNamesIn entry.path ext
      if includeDirs? then
        if mods.isEmpty then
          return #[]
        else
          return mods.push n
      else return mods
    else if entry.path.extension == some ext then
      return #[FilePath.withExtension entry.fileName "" |>.toString.toName]
    else return #[]

def importsForLib (dir : FilePath) (root : Name) (lt : Name → Name → Bool) : IO String := do
  let files ← moduleNamesIn (dir / root.toString)
  let filesSorted := files.qsort lt
  filesSorted.foldlM (init := "") fun imports fileName ↦
      return imports ++ s!"import {(root ++ fileName).toString}\n"

script import_all do
  let pkg ← Workspace.root <$> getWorkspace
  IO.println s!"Creating imports for package {pkg.name} ...\n"
  for lib in pkg.leanLibs do
    for root in lib.config.roots do
      let dir := lib.srcDir.normalize
      let fileName : FilePath := dir / (root.toString ++ ".lean")
      let imports ← importsForLib dir root (·.toString < ·.toString)
      IO.FS.writeFile fileName imports
      IO.println s!"Created imports file {fileName} for {root} library."
  return 0

script import_all? do
  let pkg ← Workspace.root <$> getWorkspace
  IO.println s!"Checking imports for package {pkg.name} ...\n"
  for lib in pkg.leanLibs do
    for root in lib.config.roots do
      let dir := lib.srcDir.normalize
      let fileName : FilePath := dir / (root.toString ++ ".lean")
      let allImports ← importsForLib dir root (·.toString < ·.toString)
      let existingImports ← IO.FS.readFile fileName
      unless existingImports == allImports do
        IO.eprintln s!"Invalid import list for {root} library."
        IO.eprintln s!"Try running `lake run mkImports`."
        return 1
  IO.println s!"The imports for package {pkg.name} are up to date."
  return 0

end Scripts
