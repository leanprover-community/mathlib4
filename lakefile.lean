import Lake

open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := #[
  "-DwarningAsError=true"
] ++ moreServerArgs

package mathlib where
  moreServerArgs := moreServerArgs

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := moreLeanArgs

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master"
require Cli from git "https://github.com/mhuisi/lean4-cli.git" @ "nightly"
require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4" @ "v0.0.11"

lean_lib Cache where
  moreLeanArgs := moreLeanArgs
  roots := #[`Cache]

lean_exe cache where
  root := `Cache.Main

lean_lib MathlibExtras where
  roots := #[`MathlibExtras]

lean_lib Archive where
  roots := #[`Archive]

lean_lib Counterexamples where
  roots := #[`Counterexamples]

lean_lib ImportGraph where
  roots := #[`ImportGraph]

lean_exe graph where
  root := `ImportGraph.Main
  supportInterpreter := true

section Scripts

open System

partial def moduleNamesIn (dir : FilePath) (ext := "lean") : IO (Array Name) :=
  dir.readDir >>= Array.concatMapM fun entry ↦ do
    if (← entry.path.isDir) then
      let n := entry.fileName.toName
      let mods ← Array.map (n ++ ·) <$> moduleNamesIn entry.path ext
      if mods.isEmpty then
        return #[]
      else
        return mods.push n
    else if entry.path.extension == some ext then
      return #[FilePath.withExtension entry.fileName "" |>.toString.toName]
    else return #[]

def importsForLib (dir : FilePath) (root : Name) : IO String := do
  moduleNamesIn (dir / root.toString) >>=
    Array.mapM (return .mkSimple root.toString ++ ·) >>=
    Array.foldlM (init := "") fun imports fileName ↦
      return imports ++ s!"import {fileName.toString}\n"

script import_all do
  let pkg ← Workspace.root <$> getWorkspace
  IO.println s!"Creating imports for package {pkg.name} ...\n"
  for lib in pkg.leanLibs do
    for root in lib.config.roots do
      let dir := lib.srcDir.normalize
      let fileName : FilePath := dir / (root.toString ++ ".lean")
      let imports ← importsForLib dir root
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
      let allImports ← importsForLib dir root
      let existingImports ← IO.FS.readFile fileName
      unless existingImports == allImports do
        IO.eprintln s!"Invalid import list for {root} library."
        IO.eprintln s!"Try running `lake run mkImports`."
        return 1
  IO.println s!"The imports for package {pkg.name} are up to date."
  return 0

end Scripts
