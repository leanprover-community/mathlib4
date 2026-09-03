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
variable (`parseOptions`).
-/

namespace Cache.Workflow.Public

open Cache.Requests
open System (FilePath)

/-- The workflow's name in messages. -/
def name : String := "public cache"

/-- The flags of the workflow: none beyond `--repo`. -/
def flags : Array Cli.Flag := #[]

/--
Check the parsed command line `p` and the environment for the workflow: no
flag of another workflow, and neither `MATHLIB_CACHE_FROM` nor
`MATHLIB_CACHE_REPO_SCOPE` set. Both variables address container chains and
per-commit namespaces, which this workflow has none of; a set one is a
misdirected read or write and fails.
-/
def parseOptions (p : Cli.Parsed) : IO Unit := do
  rejectForeignFlags name flags p
  if let some chain ← getEnvNonEmpty "MATHLIB_CACHE_FROM" then
    IO.eprintln s!"MATHLIB_CACHE_FROM={chain} is set, but the {name} workflow reads one URL \
      and has no container chain. Unset it."
    IO.Process.exit 1
  if let some scope ← Scope.ofEnv then
    IO.eprintln s!"MATHLIB_CACHE_REPO_SCOPE={scope.sha} is set, but the {name} workflow has no \
      per-commit namespaces. Unset it."
    IO.Process.exit 1

/--
The URL a public-cache read fetches from: `getURL?` (`MATHLIB_CACHE_GET_URL`,
a third party's own endpoint), else the public cache's flat namespace under
the public read base (`publicCacheURL`), `https://cache.mathlib.org/mathlib4`
by default. A file is read flat at `{url}/f/{hash}.ltar`.

The public endpoint serves the master-built artifacts and the older `legacy`
artifacts behind that namespace, so the workflow needs no fallback of its own.
-/
def url (getURL? : Option String) : IO String := do
  match getURL? with
  | some u => return u
  | none => return publicCacheURL (← getBaseURL .published)

/-- The read: one flat round at `url`. -/
def get (ctx : ReadContext) (req : ReadRequest) : IO.CacheM Unit := do
  getFiles [{ container? := none, url := ← url ctx.getURL? }] MATHLIBREPO req.hashMap
    req.forceDownload req.forceDownload req.parallel req.decompress

end Cache.Workflow.Public
