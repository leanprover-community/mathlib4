/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Workflow.Defs

/-!
# The public-cache workflow

The workflow of a canonical mathlib checkout, of a project that depends on
Mathlib, and of a read pointed at an external endpoint with
`MATHLIB_CACHE_GET_URL`. A read is one fetch from one URL: no container chain,
no per-commit scope, no marker probe, no security notice. CI publishes the
master builds this workflow reads into the `master` container.

The workflow has no flags of its own, and rejects every chain-read flag and
variable (`plan`).
-/

public section

namespace Cache.Workflow.Public

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "public cache"

/-- The flags of the workflow: none beyond `--repo`. -/
def flags : Array Cli.Flag := #[]

/--
The location a public-cache read fetches from: `MATHLIB_CACHE_GET_URL` (a
third party's own endpoint), read flat, else the `master` container on the
public endpoint under the read base rule (`readBase`),
`https://cache.mathlib.org/mathlib4-master` by default. A file is read flat at
`{root}/f/{hash}.ltar`.
-/
def location (s : Settings) : Location :=
  match s.getURL? with
  | some url => Location.flat url "MATHLIB_CACHE_GET_URL"
  | none => Container.master.location (readBase s publicCacheEndpoint) MATHLIBREPO none

/--
The plan of a public-cache read, `location`, from the parsed command line `p`
and the settings `s`. Fails on a flag of another workflow, and on a set
`MATHLIB_CACHE_FROM` or `MATHLIB_CACHE_REPO_SCOPE`: both address container
chains and per-commit namespaces, which this workflow has none of.
-/
def plan (p : Cli.Parsed) (s : Settings) : IO Location := do
  checkForeignFlags name flags p
  if let some chain := s.cacheFrom? then
    fail s!"MATHLIB_CACHE_FROM={chain} is set, but the {name} workflow reads one URL \
      and has no container chain. Unset it."
  if let some scope := s.repoScope? then
    fail s!"MATHLIB_CACHE_REPO_SCOPE={scope} is set, but the {name} workflow has no \
      per-commit namespaces. Unset it."
  return location s

/-- The read: one flat round at `location`, the plan. -/
def get (location : Location) (req : ReadRequest) : IO.CacheM Unit := do
  let result ← getFiles MATHLIBREPO [location] req.hashMap req.forceDownload req.forceDownload
    req.mode req.decompress
  if result.missing > 0 then warnMissing (missingFilesGenericLines result.missing)

end Cache.Workflow.Public
