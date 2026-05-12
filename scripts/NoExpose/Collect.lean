/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import NoExpose.Cli
import NoExpose.Diagnostics
import NoExpose.Env
import NoExpose.Paths
import NoExpose.Report
import NoExpose.Restore

/-!
# `NoExpose.Collect` — orchestrator for the `collect` subcommand

Owns the high-level sequence:
1. `NoExpose.Diagnostics`: patch lakefile, run `lake build`, parse log
   into `diagnostics.jsonl`. Skipped under `--skip-build`.
2. `NoExpose.Env`: open env via `withImportModules`; emit
   `exposed.jsonl`, `static_refs.jsonl`, `decl_refs.jsonl`.
3. `NoExpose.Report.build`: join everything into `report.jsonl`.
-/

open Lean

namespace NoExpose

/-- Run the env-scan portion of `collect`: opens the env once via
`withImportModules`, gathers static/decl refs, returns enumerated
candidates; then post-scans source files and writes `exposed.jsonl`. -/
unsafe def runEnvScan (_project : ProjectInfo) (modules : Array Name)
    (scopePrefix : Array Name) : IO Unit := do
  IO.FS.createDirAll dataDir
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  -- All env-dependent work happens inside `withImportModules`. The
  -- `DeclRecord` fields are stringified (and `Name` references dropped)
  -- before any iteration of the records, so the data is safe to write
  -- without lifetime worries.
  withImportModules modules
      (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    -- Static refs → static_refs.jsonl
    let refs ← collectStaticRefs
    IO.FS.withFile staticRefsPath .write fun h => writeStaticRefs env refs h
    IO.eprintln s!"[no_expose collect] wrote {refs.size} static-refs pairs to {staticRefsPath}"
    -- Per-decl refs → decl_refs.jsonl
    IO.FS.withFile declRefsPath .write fun h => writeDeclRefs env h
    IO.eprintln s!"[no_expose collect] wrote per-decl refs to {declRefsPath}"
    -- Source-driven enumeration: walk source for `@[expose]`,
    -- intersect with env decl ranges.
    let recs ← enumerate scopePrefix
    IO.FS.withFile exposedPath .write fun h => do
      for r in recs do h.putStrLn r.toJsonLine
    IO.eprintln s!"[no_expose collect] wrote {recs.size} exposed records to {exposedPath}"

/-- Run the `collect` subcommand. -/
unsafe def runCollect (args : CollectArgs) : IO UInt32 := do
  -- On every startup, restore any orphaned backups left by an
  -- interrupted previous run. (No-op if state.json is absent.)
  detectOrphan
  let project ← detectProjectInfo
  IO.eprintln s!"[no_expose collect] project: {project.name} \
    (libs: {project.libRoots})"
  -- Step 1: full build with diagnostics, unless skipped.
  unless args.skipBuild do
    if project.name.toString != "mathlib" then
      IO.eprintln s!"no_expose collect: full-build mode is Mathlib-only \
        (detected project: {project.name}); pass --skip-build."
      return 1
    let extraOff : Array System.FilePath := args.patchFiles.map .mk
    let rc ← runDiagnostics project.lakefilePath extraOff
    if rc != 0 then
      IO.eprintln s!"[no_expose collect] lake build returned {rc}; \
        diagnostics.jsonl reflects the partial log. Continuing with env scan."
  -- Step 2: env scan.
  -- For Mathlib, the canonical target is just `Mathlib` (the union module).
  -- For downstream projects, pick the first lib root.
  let modules : Array Name :=
    if project.libRoots.contains `Mathlib then #[`Mathlib]
    else project.libRoots.take 1
  let scopePrefix : Array Name :=
    if project.libRoots.contains `Mathlib then #[`Mathlib]
    else project.libRoots
  runEnvScan project modules scopePrefix
  -- Step 3: join.
  build exposedPath diagnosticsPath staticRefsPath declRefsPath reportPath
  return 0

end NoExpose
