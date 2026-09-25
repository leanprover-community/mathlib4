/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Workflow.Defs

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

namespace Cache.Workflow.Public

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "public cache"

/-- The flags of the workflow: none beyond `--repo`. -/
def flags : Array Cli.Flag := #[]

/--
The URL a public-cache read fetches from: `MATHLIB_CACHE_GET_URL` (a third
party's own endpoint), else the `master` container on the public endpoint,
under the read base rule (`Container.readURL`),
`https://cache.mathlib.org/mathlib4-master` by default. A file is read flat at
`{url}/f/{hash}.ltar`.

The public endpoint serves the artifacts of the retired `mathlib4` container
behind the `master` namespace, so the workflow needs no fallback of its own.
-/
def url (s : Settings) : String :=
  s.getURL?.getD (Container.master.readURL s publicCacheEndpoint)

/--
The plan of a public-cache read, `url`, from the parsed command line `p` and
the settings `s`. Fails on a flag of another workflow, and on a set
`MATHLIB_CACHE_FROM` or `MATHLIB_CACHE_REPO_SCOPE`: both address container
chains and per-commit namespaces, which this workflow has none of.
-/
def plan (p : Cli.Parsed) (s : Settings) : IO String := do
  checkForeignFlags name flags p
  if let some chain := s.cacheFrom? then
    fail s!"MATHLIB_CACHE_FROM={chain} is set, but the {name} workflow reads one URL \
      and has no container chain. Unset it."
  if let some scope := s.repoScope? then
    fail s!"MATHLIB_CACHE_REPO_SCOPE={scope} is set, but the {name} workflow has no \
      per-commit namespaces. Unset it."
  return url s

/-- The read: one flat round at `url`, the plan. -/
def get (url : String) (req : ReadRequest) : IO.CacheM Unit := do
  let result ← getFiles [{ container? := none, url }] MATHLIBREPO
    req.hashMap req.forceDownload req.forceDownload req.parallel req.decompress
  warnMissing result

end Cache.Workflow.Public
