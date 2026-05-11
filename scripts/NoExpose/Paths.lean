/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lake.CLI.Main

/-!
# `NoExpose.Paths` — data-artifact paths and project autodetect

Centralises every filesystem path the tool reads or writes, and the
small piece of Lake-introspection that lets `no_expose` adapt to the
current package (Mathlib, or a downstream Mathlib-using project).
-/

open Lake System

namespace NoExpose

/-- Root of the data directory the tool owns. Sibling of `lakefile.lean`. -/
def dataDir : FilePath := "scripts" / ".no_expose"

/-- Full Mathlib build log (raw `lake build` output). Several GB on a full
collection; kept by default for debuggability. -/
def buildLogPath : FilePath := dataDir / "build.log"

/-- Per-file diagnostic-message records parsed from the build log. -/
def diagnosticsPath : FilePath := dataDir / "diagnostics.jsonl"

/-- One record per `@[expose]` def/instance the env walk found. -/
def exposedPath : FilePath := dataDir / "exposed.jsonl"

/-- Per-(refModule, refName) static reference counts (with theorem split). -/
def staticRefsPath : FilePath := dataDir / "static_refs.jsonl"

/-- Per-decl direct reference lists (used for one-hop transitive closure). -/
def declRefsPath : FilePath := dataDir / "decl_refs.jsonl"

/-- Joined report — the primary input to `report` and `edit`. -/
def reportPath : FilePath := dataDir / "report.jsonl"

/-- Audit trail for `edit` runs: unified diff of every change. -/
def editsPatchPath : FilePath := dataDir / "edits.patch"

/-- Where `Restore` writes original copies before patching the lakefile or
fragile source files. Detected on every startup so an interrupted run
can be recovered. -/
def restoreDir : FilePath := dataDir / "restore"

/-- Marker file: present iff a `collect` run is mid-flight (used by
`Restore` to recognise crash recovery). -/
def restoreStatePath : FilePath := restoreDir / "state.json"

/-- Information about the current Lake package needed by the tool. -/
structure ProjectInfo where
  /-- The package name, e.g. `mathlib`. -/
  name : Lean.Name
  /-- The module names of the package's `lean_lib` targets that the tool
  should treat as "owned by this project". For Mathlib this is
  `[Mathlib, Archive, Counterexamples]` (we further filter to `Mathlib`
  for normal use). For a downstream `MyProj`: `[MyProj]`. -/
  libRoots : Array Lean.Name
  /-- Source root directories the libs cover, used to map decl-source-files
  back to "this project's files" vs imported deps. -/
  srcDirs : Array System.FilePath
  /-- The lakefile's path. May be `lakefile.lean` or `lakefile.toml`. -/
  lakefilePath : System.FilePath

/-- Inspect the current Lake workspace and produce a `ProjectInfo`. Mirrors
`scripts/mk_all.lean:26` and `scripts/lint-style.lean:34`. -/
def detectProjectInfo : IO ProjectInfo := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <| Lake.mkLoadConfig
    { elanInstall?, leanInstall?, lakeInstall? }
  let some ws ← (Lake.loadWorkspace config).toBaseIO
    | throw <| IO.userError "NoExpose: failed to load Lake workspace"
  let pkg := ws.root
  let libs := pkg.leanLibs.map fun lib => lib.config.name
  let srcDirs := pkg.leanLibs.map fun lib => pkg.dir / lib.config.srcDir
  let lakefilePath := pkg.dir / "lakefile.lean"
  return {
    name := pkg.baseName
    libRoots := libs
    srcDirs := srcDirs
    lakefilePath
  }

/-- JSON-string-escape `s`. -/
def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c    => c.toString

end NoExpose
