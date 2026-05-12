/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

/-!
# `NoExpose.Cli` — argument parsing for `lake exe no_expose`

Subcommands: `collect`, `report`, `edit`, plus `clean` for removing the
data directory.
-/

namespace NoExpose

/-- Format option for `report` output. -/
inductive ReportFormat where
  | text
  | json
  deriving Repr, BEq

structure CollectArgs where
  skipBuild : Bool := false
  /-- Extra files to insert `set_option diagnostics false` into. -/
  patchFiles : Array String := #[]

structure ReportArgs where
  paths : Array String := #[]
  format : ReportFormat := .text

structure EditArgs where
  paths : Array String := #[]
  dryRun : Bool := false
  verify : Bool := false
  forceDirty : Bool := false
  forceStale : Bool := false

inductive Subcommand where
  | help
  | collect (args : CollectArgs)
  | report  (args : ReportArgs)
  | edit    (args : EditArgs)
  | clean

/-- Top-level help text. -/
def helpText : String := "\
USAGE:
  lake exe no_expose <subcommand> [args...]

SUBCOMMANDS:
  collect [--skip-build] [--patch-file FILE]...
      Build Mathlib with `set_option diagnostics true`, walk the env,
      and write report data to scripts/.no_expose/.

  report [PATH...] [--format text|json]
      Render per-file recommendations from existing report data.
      With no PATH, renders every file in the report. Default
      `--format text` lists `safe-to-unexpose` and
      `needed-downstream` decls in each file.

  edit [PATH...] [--dry-run] [--verify] [--force-dirty] [--force-stale]
      Apply (default) or preview (--dry-run) the un-expose edits to
      each PATH. Refuses on dirty git tree or stale report unless the
      corresponding --force-* flag is given. With --verify, runs
      `lake build` on the touched lib after applying.

  clean
      Remove scripts/.no_expose/ entirely.

  help, --help, -h
      Show this message.
"

private def parseFormat : String → Except String ReportFormat
  | "text" => .ok .text
  | "json" => .ok .json
  | s      => .error s!"unknown --format value: {s} (expected text|json)"

/-- Parse a `collect` argument list. -/
private partial def parseCollect (rest : List String) : Except String CollectArgs := loop rest {} where
  loop : List String → CollectArgs → Except String CollectArgs
    | [], acc => .ok acc
    | "--skip-build" :: rest, acc => loop rest { acc with skipBuild := true }
    | "--patch-file" :: f :: rest, acc =>
      loop rest { acc with patchFiles := acc.patchFiles.push f }
    | flag :: _, _ => .error s!"collect: unknown argument {flag}"

/-- Parse a `report` argument list. -/
private partial def parseReport (rest : List String) : Except String ReportArgs := loop rest {} where
  loop : List String → ReportArgs → Except String ReportArgs
    | [], acc => .ok acc
    | "--format" :: v :: rest, acc => do
      let f ← parseFormat v
      loop rest { acc with format := f }
    | arg :: rest, acc =>
      if arg.startsWith "--" then .error s!"report: unknown flag {arg}"
      else loop rest { acc with paths := acc.paths.push arg }

/-- Parse an `edit` argument list. -/
private partial def parseEdit (rest : List String) : Except String EditArgs := loop rest {} where
  loop : List String → EditArgs → Except String EditArgs
    | [], acc => .ok acc
    | "--dry-run" :: rest, acc => loop rest { acc with dryRun := true }
    | "--verify" :: rest, acc => loop rest { acc with verify := true }
    | "--force-dirty" :: rest, acc => loop rest { acc with forceDirty := true }
    | "--force-stale" :: rest, acc => loop rest { acc with forceStale := true }
    | arg :: rest, acc =>
      if arg.startsWith "--" then .error s!"edit: unknown flag {arg}"
      else loop rest { acc with paths := acc.paths.push arg }

/-- Top-level dispatch. -/
def parseArgs : List String → Except String Subcommand
  | []                       => .ok .help
  | "help" :: _              => .ok .help
  | "--help" :: _            => .ok .help
  | "-h" :: _                => .ok .help
  | "collect" :: rest        => .collect <$> parseCollect rest
  | "report"  :: rest        => .report  <$> parseReport rest
  | "edit"    :: rest        => .edit    <$> parseEdit rest
  | "clean" :: []            => .ok .clean
  | "clean" :: rest          => .error s!"clean: unexpected arguments: {String.intercalate " " rest}"
  | sub :: _                 => .error s!"unknown subcommand: {sub} (try `--help`)"

end NoExpose
