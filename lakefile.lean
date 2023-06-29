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

section Scripts

open System

def getCurrentPackage : ScriptM Package := do
  let ws ← Lake.getWorkspace
  let [pkg] := ws.packageList.filter (·.dir = ⟨"."⟩) | throw <| IO.userError "Current package not found."
  return pkg

def importsForLib (lib : Name) : IO String := do
  let dir ← FilePath.walkDir lib.toString >>= Array.filterM (not <$> ·.isDir)
  let filePathToImport : FilePath → String := fun fp ↦ fp.toString.takeWhile (· != FilePath.extSeparator) |>.map <|
    fun c ↦ if c = FilePath.pathSeparator then '.' else c
  let imports := dir.foldl (init := "") <| fun s f ↦ s ++ s!"import {filePathToImport f}\n"
  return imports

script import_all do
  let pkg ← getCurrentPackage
  IO.println s!"Creating imports for package {pkg.name} ...\n"
  for (lib, _) in pkg.leanLibConfigs do
    let fileName : FilePath := lib.toString ++ ".lean"
    let imports ← importsForLib lib
    IO.FS.writeFile fileName imports
    IO.println s!"Created imports file for {lib} library."
  return 0

script import_all? do
  let pkg ← getCurrentPackage
  IO.println s!"Checking imports for package {pkg.name} ...\n"
  for (lib, _) in pkg.leanLibConfigs do
    let fileName : FilePath := lib.toString ++ ".lean"
    let allImports ← importsForLib lib
    let existingImports ← IO.FS.readFile fileName
    unless existingImports = allImports do
      IO.eprintln s!"Invalid import list for {lib} library."
      IO.eprintln s!"Try running `lake run import_all`."
      return 1
  IO.println s!"The imports for package {pkg.name} are up to date."
  return 0

end Scripts
