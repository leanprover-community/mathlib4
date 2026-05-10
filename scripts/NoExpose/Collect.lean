/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import NoExpose.Cli
import NoExpose.Env
import NoExpose.Paths
import NoExpose.Report

/-!
# `NoExpose.Collect` — orchestrator for the `collect` subcommand

Owns the high-level sequence:
1. (TODO) `NoExpose.Diagnostics`: patch lakefile, run `lake build`, parse log.
2. `NoExpose.Env`: open env via `withImportModules`; emit
   `exposed.jsonl`, `static_refs.jsonl`, `decl_refs.jsonl`.
3. `NoExpose.Report.build`: join everything into `report.jsonl`.

For now only step 2 + 3 are implemented (i.e. `--skip-build` mode).
-/

open Lean

namespace NoExpose

/-- Run the env-scan portion of `collect`: opens the env once via
`withImportModules`, then writes all three JSONLs. Defaults to
importing the project's lib roots. -/
unsafe def runEnvScan (project : ProjectInfo) (modules : Array Name)
    (scopePrefix : Array Name) : IO Unit := do
  IO.FS.createDirAll dataDir
  let searchPath ← addSearchPathFromEnv (← getBuiltinSearchPath (← findSysroot))
  withImportModules modules (searchPath := searchPath) (trustLevel := 1024) do
    let env ← getEnv
    -- 1. Enumeration → exposed.jsonl
    let recs ← enumerate scopePrefix
    IO.FS.withFile exposedPath .write fun h => do
      for r in recs do h.putStrLn r.toJsonLine
    IO.eprintln s!"[no_expose collect] wrote {recs.size} exposed records to {exposedPath}"
    -- 2. Static refs → static_refs.jsonl
    let refs ← collectStaticRefs
    IO.FS.withFile staticRefsPath .write fun h => writeStaticRefs env refs h
    IO.eprintln s!"[no_expose collect] wrote {refs.size} static-refs pairs to {staticRefsPath}"
    -- 3. Per-decl refs → decl_refs.jsonl
    IO.FS.withFile declRefsPath .write fun h => writeDeclRefs env h
    IO.eprintln s!"[no_expose collect] wrote per-decl refs to {declRefsPath}"
  -- Mark unused
  let _ := project

/-- Run the `collect` subcommand. -/
unsafe def runCollect (args : CollectArgs) : IO UInt32 := do
  let project ← detectProjectInfo
  IO.eprintln s!"[no_expose collect] project: {project.name} \
    (libs: {project.libRoots})"
  unless args.skipBuild do
    IO.eprintln "no_expose collect: full build mode not yet implemented; \
      pass --skip-build to use existing oleans + diagnostics.jsonl."
    return 1
  -- For Mathlib, the canonical target is just `Mathlib` (the union module).
  -- For downstream projects, pick the first lib root.
  let modules : Array Name :=
    if project.libRoots.contains `Mathlib then #[`Mathlib]
    else project.libRoots.take 1
  let scopePrefix : Array Name :=
    if project.libRoots.contains `Mathlib then #[`Mathlib]
    else project.libRoots
  runEnvScan project modules scopePrefix
  -- Now build report.jsonl by joining everything.
  build exposedPath diagnosticsPath staticRefsPath declRefsPath reportPath
  return 0

end NoExpose
