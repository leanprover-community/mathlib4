/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Cli
import Cache.Requests

/-!
# What the read workflows receive

The inputs a `get` resolves before it chooses a workflow, in the shape the
workflow modules take them: the transfer itself (`ReadRequest`), and the
repository and the settings of the read (`ReadContext`). Each workflow parses
its own flags from the parsed command line; the check a workflow uses to
reject what is not its own (`checkForeignFlags`) and the missing-files warning
they share (`warnMissing`) live here too.

The workflow layer reads no environment variable and does not exit: a
workflow takes the settings from `ReadContext`, and an invalid option throws
(`fail`), which the command reports (`Cache.Commands`).
-/

namespace Cache.Workflow

open Cache.Requests
open System (FilePath)

/-- The transfer a `get` performs, the same under every workflow. -/
structure ReadRequest where
  /-- The files to read. -/
  hashMap : IO.ModuleHashMap
  /-- Re-download files already in the local cache. -/
  forceDownload : Bool
  /-- Decompress as the files arrive. -/
  decompress : Bool
  /-- Transfer in parallel (curl is recent enough). -/
  parallel : Bool

/-- The repository a read is for, resolved by the command (see `resolveRepo`),
and the settings of the read. -/
structure ReadContext where
  /-- The `--repo=` value, if given; the notice compares it with `detectedRepo?`. -/
  repoExplicit? : Option String
  /-- The resolved repo the read is for. -/
  repo : String
  /-- The repo the git remote reports, if any. -/
  detectedRepo? : Option String
  /-- The environment of the read. -/
  settings : Settings := {}
  /-- The mathlib checkout the git probes run in: `.` on a mathlib checkout,
  the dependency checkout when Mathlib is a dependency. -/
  mathlibCwd : FilePath

/-- The flags of the parsed command line `p` that are neither common
(`CommonFlag.names`) nor among a workflow's `own` flags. -/
def foreignFlags (own : Array Cli.Flag) (p : Cli.Parsed) : Array Cli.Parsed.Flag :=
  p.flags.filter fun f =>
    !CommonFlag.names.contains f.flag.longName && !own.any (·.longName == f.flag.longName)

/-- Fail the read with `msg`; the command prints it and exits with 1. -/
def fail (msg : String) : IO α := throw (IO.userError msg)

/--
Fail on the flags of the parsed command line `p` that belong to another
workflow (`foreignFlags own p`). The command declares the union of all
workflows' flags, so each such flag is another workflow's, and the message
names the `workflow` that does not take it.
-/
def checkForeignFlags (workflow : String) (own : Array Cli.Flag) (p : Cli.Parsed) : IO Unit := do
  let foreign := foreignFlags own p
  unless foreign.isEmpty do
    let names := ", ".intercalate (foreign.toList.map fun f => s!"--{f.flag.longName}")
    fail s!"{names}: not an option of the {workflow} workflow."

/--
Print the warning for the files no round served (`ReadResult.missing`), with
the workflow's own `hints` after the ones every read shares.
-/
def warnMissing (result : ReadResult) (hints : List String := []) : IO Unit := do
  if result.missing == 0 then return
  let lines := [
    s!"Warning: {result.missing} file(s) were not found in the cache.",
    "This usually means that your local checkout of mathlib4 has diverged from upstream.",
    "",
    "  * If you push your commits to a PR to the mathlib4 repository",
    "    (use a draft PR if it is not ready for review),",
    "    then CI will build the oleans and they will be available later.",
    "  * If you have already opened a PR, this may mean",
    "    the CI build has failed part-way through building."] ++ hints
  for line in lines do
    IO.eprintln line

end Cache.Workflow
