import Lake

open Lake DSL System

package mathlib

@[default_target]
lean_lib Mathlib where
  moreLeanArgs := #[
    "-DwarningAsError=true",
    "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
  ]

@[default_target]
lean_exe runLinter where
  root := `scripts.runLinter
  supportInterpreter := true

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master"

lean_lib Cache where
  roots := #[`Cache]

lean_exe cache where
  root := `Cache.Main

/-! Widget build -/

def npmCmd : String :=
  if Platform.isWindows then "npm.cmd" else "npm"

def widgetDir := __dir__ / "widget"

target widgetPackageLock : FilePath := do
  let packageFile ← inputFile <| widgetDir / "package.json"
  let packageLockFile := widgetDir / "package-lock.json"
  buildFileAfterDep packageLockFile packageFile fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["install"]
      cwd := some widgetDir
    }

def widgetTsxTarget (pkg : Package) (tsxName : String) (deps : Array (BuildJob FilePath))
    [Fact (pkg.name = _package.name)] : IndexBuildM (BuildJob FilePath) := do
  let jsFile := widgetDir / "dist" / s!"{tsxName}.js"
  let deps := deps ++ #[
    ← inputFile <| widgetDir / "src" / s!"{tsxName}.tsx",
    ← inputFile <| widgetDir / "rollup.config.js",
    ← inputFile <| widgetDir / "tsconfig.json",
    ← fetch (pkg.target ``widgetPackageLock)
  ]
  buildFileAfterDepArray jsFile deps fun _srcFile => do
    proc {
      cmd := npmCmd
      args := #["run", "build", "--", "--tsxName", tsxName]
      cwd := some widgetDir
    }

target widgetCommDiag (pkg : Package) : FilePath := do
  let files : Array FilePath := #[
    "penrose.tsx",
    "penrose" / "commutative.dsl",
    "penrose" / "commutative.sty",
    "penrose" / "square.sub",
    "penrose" / "triangle.sub"
  ]
  widgetTsxTarget pkg "commDiag" (← files.mapM fun f => inputFile (widgetDir / "src" / f))
