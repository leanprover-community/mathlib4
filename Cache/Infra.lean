/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch, Arthur Paulino
-/
module

public import Cache.Env

/-!
# Cache backend infrastructure

The multi-container model: the trust-classified storage containers, the
per-repo lookup chain, and the GitHub repo names that the cache tool dispatches on.

This lives apart from `Cache.Requests` so the container model and trust ordering
stand on their own, independent of the HTTP/curl machinery that consumes them.
-/

public section

namespace Cache.Requests

open System (FilePath)

/-- The full name of the main Mathlib GitHub repository. -/
def MATHLIBREPO := "leanprover-community/mathlib4"

/-- Whether `repo` is the canonical Mathlib repo. Every other repo, nightly-testing
included, caches into the per-commit `forks` namespace. -/
def isCanonicalRepo (repo : String) : Bool :=
  repo == MATHLIBREPO

/--
Canonical form of a GitHub `owner/repo` name for use as a cache blob path
segment.

GitHub treats owner and repository names case-insensitively, while storage
paths are case-sensitive. Lowercasing yields one shared key whatever
capitalization a remote URL or the GitHub Actions context supplies, so a fork's
uploads and downloads always meet at the same path.
-/
def normalizeRepo (repo : String) : String := repo.toLower

/--
Trust-classified storage containers for the Mathlib cache.

A container is a namespace in the URL contract `/{container}/{key}` that
every cache host serves. `Container.location` resolves a container to a
`Location`. A CI job at a given trust level may write only to its
corresponding container, and `cache get` tries the most trusted container
first.
-/
inductive Container where
  /-- Most-trusted container (`mathlib4-master`); only master CI writes here. -/
  | master
  /-- Container for fork PR builds, mathlib4 development branches, and every
  push build on the nightly-testing repo. -/
  | forks
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Base URL of the `lakecache` Azure Blob Storage account. -/
def azureAccountURL : String := "https://lakecache.blob.core.windows.net"

namespace Container

/-- Canonical short name for a container, used in CLI flags and URLs. -/
def name : Container → String
  | .master => "master"
  | .forks  => "forks"

/-- All known containers, listed in their canonical declaration order. -/
def all : List Container :=
  [.master, .forks]

/-- Parse a short name back into a `Container`. Matching is case-insensitive. -/
def parse? (s : String) : Option Container :=
  match s.toLower with
  | "master" => some .master
  | "forks"  => some .forks
  | _        => none

/--
The container's segment in the URL contract `{base}/{pathSegment}/{key}`
(`Container.urlUnder`). A bucket backend uses the same string as its key
prefix.

Every container follows the `mathlib4-{name}` convention.
-/
def pathSegment (c : Container) : String :=
  s!"mathlib4-{c.name}"

/-- The container's URL under `base`: `{base}/{pathSegment}`. `base` is a host
or an upload base that serves the `/{container}/{key}` namespace. -/
def urlUnder (c : Container) (base : String) : String :=
  s!"{base}/{c.pathSegment}"

/-- Public Azure Blob Storage base URL for a container. -/
def azureURL (c : Container) : String :=
  c.urlUnder azureAccountURL

/--
Whether file lookups in this container use the flat `/f/<hash>` layout, or
namespace under `/f/<repo>/<hash>`.

The layout is fixed per container, not per repo, because one container holds
artifacts from several writers whose `repo` need not match the container's
trust level, and a stable per-container layout is what keeps readers and
writers in sync.

- `master` is flat: RBAC admits only master CI, whose writes all carry
  `repo == MATHLIBREPO`, so a single hash never collides.
- `forks` always namespaces by repo. It collects artifacts from many writers —
  different forks, the nightly-testing repo, and canonical-repo builds whose
  trust is fork-equivalent (`ci-dev/*`, `bors trying`) — so identical hashes
  from different writers must stay on distinct paths.
-/
def flatPath : Container → Bool
  | .master => true
  | .forks => false

end Container

/--
The public Mathlib cache endpoint. It serves the same `/{container}/{key}`
namespace as the storage account and caches artifacts at its edge, so reads
cost the project less and land nearer the reader.
-/
def publicCacheEndpoint : String := "https://cache.mathlib.org"

/--
Whether reads of the `master` container address the Azure storage account
instead of `publicCacheEndpoint`. `main` sets this from
`MATHLIB_CACHE_DEBUG_USE_LEGACY` at startup. Every other container reads from
`publicCacheEndpoint` either way.

The variable is a troubleshooting fallback for the transition to the public
endpoint, enabled in September 2026, and it should be retired together with
direct reads from the storage account.
-/
initialize useLegacy : IO.Ref Bool ← IO.mkRef false

/--
Default base URL for reads of container `c`: `publicCacheEndpoint`, or
`azureAccountURL` for the `master` container when `useLegacy` is set.
-/
def defaultGetBaseURL (c : Container) (useLegacy : Bool) : String :=
  if useLegacy && c == .master then azureAccountURL else publicCacheEndpoint

/--
Base URL for reads of container `c`: `MATHLIB_CACHE_BASE_URL` if set,
otherwise `defaultGetBaseURL c useLegacy`. `normalizeBaseURL` reads the value, so it
arrives trimmed, free of trailing slashes, and unset when empty.

A read URL is `{base}/{pathSegment}/{key}`, the namespace every cache
host serves. Any host that mirrors that namespace is therefore a valid base.
This override differs from `MATHLIB_CACHE_GET_URL`. That variable serves
external consumers: it names one flat endpoint and bypasses the container
lookup chain. `MATHLIB_CACHE_BASE_URL` serves internal consumers, that is,
CI and contributors to the mathlib4 repository. It keeps the lookup chain and
rebases each container read under the given host.

Only reads follow this base. Uploads and marker writes use the location of
the selected backend (`uploadLocation`).
-/
def getBaseURLFrom (c : Container) (envValue? : Option String) (useLegacy : Bool) : String :=
  (normalizeBaseURL envValue?).getD (defaultGetBaseURL c useLegacy)

/--
Base URL for reads of container `c`, resolved from the environment.
Written on top of the pure function above, which is separate to be testable.
-/
def getBaseURL (c : Container) : BaseIO String := do
  return getBaseURLFrom c (← IO.getEnv "MATHLIB_CACHE_BASE_URL") (← useLegacy.get)

/--
Comma-separated list parser for `--cache-from=a,b,c`.

Returns `none` if any element is unrecognized.
-/
def parseCacheFromList (s : String) : Option (List Container) := do
  let parts := s.splitOn ","
  parts.mapM (fun p => Container.parse? p.trimAscii.toString)

/--
Trust-ordered containers to try when downloading for a given GitHub repo, most
trusted first. Each repo reads from its own trust-level container.

Fork chains lead with `master`. The layout is fixed per container
(`Container.flatPath`), so the `master` container is read flat at `/f/{hash}`
whatever the `repo` is, and a fork build finds the master-built deps that make
up the bulk of its files there; the fork's own container then supplies the
PR-specific files at `/f/{repo}/...`.

The nightly-testing repo is a fork in this model.
-/
def defaultContainersForRepo (repo : String) : List Container :=
  if repo == MATHLIBREPO then
    [.master]
  else
    -- Forks and everything else: `master` for shared upstream deps, the fork's
    -- own container for PR-specific files.
    [.master, .forks]
