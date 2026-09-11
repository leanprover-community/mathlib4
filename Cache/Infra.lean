/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch, Arthur Paulino
-/

import Cache.Env

/-!
# Cache backend infrastructure

The multi-container model — trust-classified Azure containers and the per-repo
lookup chain — together with the GitHub repo names the cache tool dispatches on.

This lives apart from `Cache.Requests` so the container model and trust ordering
stand on their own, independent of the HTTP/curl machinery that consumes them.
-/

namespace Cache.Requests

open System (FilePath)

/-- The full name of the main Mathlib GitHub repository. -/
def MATHLIBREPO := "leanprover-community/mathlib4"

/-- The full name of the Mathlib nightly-testing GitHub repository. -/
def NIGHTLY_TESTING_REPO := "leanprover-community/mathlib4-nightly-testing"

/-- Whether `repo` is a first-party Mathlib repo rather than a fork. Forks cache
into the per-commit `forks` namespace; the canonical repos do not. -/
def isCanonicalRepo (repo : String) : Bool :=
  repo == MATHLIBREPO || repo == NIGHTLY_TESTING_REPO

/--
Canonical form of a GitHub `owner/repo` name for use as a cache blob path
segment.

GitHub treats owner and repository names case-insensitively, while Azure Blob
Storage paths are case-sensitive. Lowercasing yields one shared key whatever
capitalization a remote URL or the GitHub Actions context supplies, so a fork's
uploads and downloads always meet at the same path.
-/
def normalizeRepo (repo : String) : String := repo.toLower

/--
Trust-classified Azure storage containers for the Mathlib cache.

Each variant maps to one Azure Blob Storage container on the `lakecache` storage
account. A CI job at a given trust level may write only to its corresponding
container, and `cache get` always tries the most trusted container first.
-/
inductive Container where
  /-- Most-trusted container (`mathlib4-master`); only master CI writes here. -/
  | master
  /-- Container for PR builds on forks of mathlib4. -/
  | forks
  /-- Container for the `nightly-testing` branch and related refs. -/
  | nightlyTesting
  /-- Container for toolchain-PR test runs. -/
  | prToolchainTests
  /-- The bare `mathlib4` container that older cache clients read from. CI does
  not upload here; it is a read-only store of the master-built artifacts that
  were mirrored from `mathlib4-master`, kept reachable so those older clients
  can resolve them. The `master` container is a self-contained cache, so reads
  fall back to `legacy` only for artifacts predating the write cutover. -/
  | legacy
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Base URL of the `lakecache` Azure Blob Storage account. -/
def azureAccountURL : String := "https://lakecache.blob.core.windows.net"

namespace Container

/-- Canonical short name for a container, used in CLI flags and URLs. -/
def name : Container → String
  | .master           => "master"
  | .forks            => "forks"
  | .nightlyTesting   => "nightly-testing"
  | .prToolchainTests => "pr-toolchain-tests"
  | .legacy           => "legacy"

/-- All known containers, listed in their canonical declaration order. -/
def all : List Container :=
  [.master, .forks, .nightlyTesting, .prToolchainTests, .legacy]

/-- Parse a short name back into a `Container`. Matching is case-insensitive. -/
def parse? (s : String) : Option Container :=
  match s.toLower with
  | "master"             => some .master
  | "forks"              => some .forks
  | "nightly-testing"    => some .nightlyTesting
  | "pr-toolchain-tests" => some .prToolchainTests
  | "legacy"             => some .legacy
  | _                    => none

/--
Azure storage container name on the `lakecache` storage account.

Trust-level containers follow the `mathlib4-{name}` convention; `legacy` is the
bare `mathlib4` container.
-/
def azureContainerName : Container → String
  | .legacy => "mathlib4"
  | c       => s!"mathlib4-{c.name}"

/-- Public Azure Blob Storage base URL for a container. -/
def azureURL (c : Container) : String :=
  s!"{azureAccountURL}/{c.azureContainerName}"

/--
Whether file lookups in this container use the flat `/f/<hash>` layout, or
namespace under `/f/<repo>/<hash>`.

The layout is fixed per container, not per repo, because one container holds
artifacts from several writers whose `repo` need not match the container's
trust level, and a stable per-container layout is what keeps readers and
writers in sync.

- `master` is flat: RBAC admits only master CI, whose writes all carry
  `repo == MATHLIBREPO`, so a single hash never collides.
- `legacy` keys the layout on the writer: `MATHLIBREPO` writes are flat (where
  older `mathlib4` readers look for them), fork writes are repo-namespaced.
- `forks`, `nightly-testing`, and `pr-toolchain-tests` always namespace by
  repo. They collect artifacts from many writers — different forks, different
  toolchain refs, and canonical-repo builds whose trust is fork-equivalent
  (`ci-dev/*`, `bors trying`) — so identical hashes from different writers must
  stay on distinct paths.
-/
def flatPath (c : Container) (repo : String) : Bool :=
  match c with
  | .master => true
  | .legacy => repo == MATHLIBREPO
  | _ => false

end Container

/--
The public Mathlib cache endpoint. It serves the same `/{container}/{key}`
namespace as the storage account and caches artifacts at its edge, so reads
cost the project less and land nearer the reader.
-/
def publicCacheEndpoint : String := "https://cache.mathlib.org"

/--
Whether reads address the Azure storage account instead of
`publicCacheEndpoint`. `main` sets this from `MATHLIB_CACHE_DEBUG_USE_LEGACY`
at startup.

The variable is a troubleshooting fallback for the transition to the public
endpoint, enabled in September 2026, and it should be retired together with
direct reads from the storage account.
-/
initialize useLegacy : IO.Ref Bool ← IO.mkRef false

/--
Default base URL for cache reads: `publicCacheEndpoint`, or `azureAccountURL`
when `useLegacy` is set.
-/
def defaultGetBaseURL (useLegacy : Bool) : String :=
  if useLegacy then azureAccountURL else publicCacheEndpoint

/--
Base URL for cache reads: `MATHLIB_CACHE_BASE_URL` if set, otherwise
`defaultGetBaseURL useLegacy`. `normalizeBaseURL` reads the value, so it
arrives trimmed, free of trailing slashes, and unset when empty.

A read URL is `{base}/{azureContainerName}/{key}`, the namespace the Azure
account serves. Any host that mirrors that namespace is therefore a valid base.
This override differs from `MATHLIB_CACHE_GET_URL`. That variable serves
external consumers: it names one flat endpoint and bypasses the container
lookup chain. `MATHLIB_CACHE_BASE_URL` serves internal consumers, that is,
CI and contributors to the mathlib4 repository. It keeps the lookup chain and
rebases each container read under the given host.

Only reads follow this base. Uploads, marker writes, and the blob-listing
query authenticate against Azure and use `Container.azureURL` directly.
-/
def getBaseURLFrom (envValue? : Option String) (useLegacy : Bool) : String :=
  (normalizeBaseURL envValue?).getD (defaultGetBaseURL useLegacy)

/--
Base URL for cache reads, resolved from the environment.
Written on top of the pure function above, which is separate to be testable.
-/
def getBaseURL : IO String := do
  return getBaseURLFrom (← IO.getEnv "MATHLIB_CACHE_BASE_URL") (← useLegacy.get)

/-- Read URL for a container: `{getBaseURL}/{azureContainerName}`. -/
def Container.getURL (c : Container) : IO String := do
  return s!"{← getBaseURL}/{c.azureContainerName}"

/--
Comma-separated list parser for `--cache-from=a,b,c`.

Returns `none` if any element is unrecognized.
-/
def parseCacheFromList (s : String) : Option (List Container) := do
  let parts := s.splitOn ","
  parts.mapM (fun p => Container.parse? p.trimAscii.toString)

/--
Trust-ordered containers to try when downloading for a given GitHub repo, most
trusted first. Each repo reads from its own trust-level container, with `legacy`
appended so older clients' artifacts stay reachable.

Fork chains lead with `master`. The layout is fixed per container
(`Container.flatPath`), so the `master` container is read flat at `/f/{hash}`
whatever the `repo` is, and a fork build finds the master-built deps that make
up the bulk of its files there; the fork's own container then supplies the
PR-specific files at `/f/{repo}/...`.

Nightly-testing chains omit `master`: that repo builds under a non-release
toolchain, so its root hash differs and a master probe never matches.
-/
def defaultContainersForRepo (repo : String) : List Container :=
  if repo == MATHLIBREPO then
    [.master, .legacy]
  else if repo == NIGHTLY_TESTING_REPO then
    -- `forks` is needed for PRs opened from this repo into mathlib4: their CI
    -- uploads land in `forks`. `pr-toolchain-tests` is excluded.
    [.nightlyTesting, .forks, .legacy]
  else
    -- Forks and everything else: `master` for shared upstream deps, the fork's
    -- own container for PR-specific files, then `legacy`.
    [.master, .forks, .legacy]
