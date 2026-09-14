/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch, Arthur Paulino
-/

import Cache.Env

/-!
# Cache backend infrastructure

The multi-container model — trust-classified containers, the public/developer
service split, and the per-repo lookup chain — together with the GitHub repo
names the cache tool dispatches on.

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
Trust-classified storage containers for the Mathlib cache.

A container is a logical namespace in the URL contract `/{container}/{key}`,
not a particular storage technology: each variant is served by whatever
backend its service's endpoint resolves to. The Azure Blob Storage account
(`lakecache`) serves the same namespaces as its own containers, which is what
the legacy switch addresses directly. A CI job at a given trust level may
write only to its corresponding container, and `cache get` always tries the
most trusted container first.
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

/--
The two artifact services the cache is split across. Each service has its own
storage, read endpoint, and write credential flow, so work-in-progress
artifacts never share infrastructure with the artifacts the public consumes.

* `published`: the public service — the master-built cache that anyone, a
  mathlib checkout or a downstream project, may consume. Written only by
  master-trust CI. (The constructor is not named `public` because that is a
  reserved keyword.)
* `developer`: the developer cache — work-in-progress artifacts from
  fork PR builds, the nightly-testing repo, and toolchain experiments. Mathlib checkouts (canonical or fork) read it; a downstream
  project's default lookup reaches it only for the first-party
  `nightly-testing` container, when the dependency itself is the
  nightly-testing repo (see `defaultContainersFor`).
-/
inductive Service where
  | published
  | developer
  deriving DecidableEq, Repr, BEq, Inhabited

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

/-- Parse a short name back into a `Container`: the inverse of `name` over
`all`, so the three stay in agreement by construction. Matching is
case-insensitive. -/
def parse? (s : String) : Option Container :=
  all.find? (·.name == s.toLower)

/--
The container's segment in the URL contract: read URLs are
`{base}/{pathSegment}/{key}`, and a bucket backend uses the same string as its
key prefix. The segment doubles as the Azure storage container name on the
`lakecache` account, which is why `Container.azureURL` reuses it.

Trust-level containers follow the `mathlib4-{name}` convention; `legacy` is the
bare `mathlib4` segment.
-/
def pathSegment : Container → String
  | .legacy => "mathlib4"
  | c       => s!"mathlib4-{c.name}"

/-- Public Azure Blob Storage base URL for a container. -/
def azureURL (c : Container) : String :=
  s!"{azureAccountURL}/{c.pathSegment}"

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

/--
The service a container belongs to.

`master` and `legacy` hold only master-built artifacts, so they are the public
service. The other three collect work-in-progress uploads — fork PRs,
nightly-testing branches, toolchain experiments — and form the developer
cache. The mapping decides which read endpoint serves a container and which
storage its writers authenticate against.
-/
def service : Container → Service
  | .master | .legacy => .published
  | .forks | .nightlyTesting | .prToolchainTests => .developer

end Container

/--
The path prefix between `f/` and the file name, per the container's layout
policy (`Container.flatPath`): empty for a flat container, `{repo}/` for a
repo-namespaced one, `{repo}/{scope}/` when a per-SHA scope applies. `repo` is
lowercased via `normalizeRepo`. `mkFileURL` and the staged-upload destination
(`stagedUploadDestFrom`) both build on this, so reads, curl uploads, and
hook uploads share one path contract by construction.
-/
def filePathPrefix (container : Option Container) (repo : String)
    (repoScope : Option String) : String :=
  let repo := normalizeRepo repo
  let flat := match container with
    | some c => c.flatPath repo
    | none => repo == MATHLIBREPO
  if flat then ""
  else match repoScope with
    | some s => s!"{repo}/{s}/"
    | none => s!"{repo}/"


/--
Blob path of the directory that holds a repo's per-SHA markers: `m/{repo}`,
with `repo` lowercased via `normalizeRepo`. A marker for one commit lives at
`{markerDirPath repo}/{sha}`; its presence signals that the writing `put`
completed its upload to that destination.
-/
def markerDirPath (repo : String) : String :=
  s!"m/{normalizeRepo repo}"

/-- Blob path of the per-SHA marker: `m/{repo}/{sha}` (see `markerDirPath`). -/
def markerPath (repo sha : String) : String :=
  s!"{markerDirPath repo}/{sha}"

/--
The public Mathlib cache endpoint. It serves the master-built artifacts under
the same `/{container}/{key}` namespace as the storage account and caches them
at its edge, so reads cost the project less and land nearer the reader.
-/
def publicCacheEndpoint : String := "https://cache.mathlib.org"

/--
The developer cache endpoint: the read endpoint for the developer cache's
containers (`forks`, `nightly-testing`, `pr-toolchain-tests`). It serves the
same `/{container}/{key}` namespace shape as `publicCacheEndpoint`, backed by
the storage that holds the work-in-progress artifacts.

Mathlib checkouts (canonical or fork) read here. A downstream project's
default lookup chain reaches it only for the first-party `nightly-testing`
container, when the dependency itself is the nightly-testing repo (see
`defaultContainersFor`).
-/
def developerCacheEndpoint : String := "https://devcache.mathlib.org"

/-- The endpoint a service's reads default to. -/
def Service.endpoint : Service → String
  | .published => publicCacheEndpoint
  | .developer => developerCacheEndpoint

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
Default base URL for cache reads from `service`: the service's endpoint, or
`azureAccountURL` when `useLegacy` is set. The Azure account holds every
container, so the legacy switch sends both services to the one host.
-/
def defaultGetBaseURL (service : Service) (useLegacy : Bool) : String :=
  if useLegacy then azureAccountURL else service.endpoint

/--
Base URL for cache reads from `service`.

Precedence:
1. `MATHLIB_CACHE_DEVELOPER_BASE_URL` (`developerEnv?`), for the developer cache
   only: the read host for the developer cache's containers alone.
2. `MATHLIB_CACHE_BASE_URL` (`baseEnv?`), for both services: a host that
   mirrors the whole `/{container}/{key}` namespace. Setting only this variable
   keeps every read on one host.
3. `defaultGetBaseURL service useLegacy`.

`normalizeBaseURL` reads both values, so they arrive trimmed, free of trailing
slashes, and unset when empty.

A read URL is `{base}/{pathSegment}/{key}`, the one namespace shape every
backend serves. Any host that mirrors that namespace for the service's
containers is therefore a valid base. These overrides differ from
`MATHLIB_CACHE_GET_URL`. That variable serves external consumers: it names one
flat endpoint and bypasses the container lookup chain. The base URLs serve
mathlib's own consumers, that is, CI and contributors to the repository.
They keep the lookup chain and rebase each container read under the given host.

Only reads follow these bases. Uploads resolve their own destination (see
`stagedUploadDest`).
-/
def getBaseURLFrom (service : Service) (baseEnv? developerEnv? : Option String)
    (useLegacy : Bool) : String :=
  let developer? := if service == .developer then normalizeBaseURL developerEnv? else none
  (developer? <|> normalizeBaseURL baseEnv?).getD (defaultGetBaseURL service useLegacy)

/--
Base URL for cache reads from `service`, resolved from the environment.
Written on top of the pure function above, which is separate to be testable.
-/
def getBaseURL (service : Service) : IO String := do
  return getBaseURLFrom service (← IO.getEnv "MATHLIB_CACHE_BASE_URL")
    (← IO.getEnv "MATHLIB_CACHE_DEVELOPER_BASE_URL") (← useLegacy.get)

/-- Read URL for a container: `{getBaseURL c.service}/{pathSegment}`. -/
def Container.getURL (c : Container) : IO String := do
  return s!"{← getBaseURL c.service}/{c.pathSegment}"

/--
Comma-separated list parser for `--cache-from=a,b,c`.

Returns `none` if any element is unrecognized.
-/
def parseCacheFromList (s : String) : Option (List Container) := do
  let parts := s.splitOn ","
  parts.mapM (fun p => Container.parse? p.trimAscii.toString)

/--
Trust-ordered containers a developer read tries for a given GitHub repo,
most trusted first. Each repo reads from its own trust-level container, with `legacy`
appended so older clients' artifacts stay reachable.

Fork chains lead with `master`. The layout is fixed per container
(`Container.flatPath`), so the `master` container is read flat at `/f/{hash}`
whatever the `repo` is, and a fork build finds the master-built deps that make
up the bulk of its files there; the fork's own container then supplies the
PR-specific files at `/f/{repo}/...`.

Nightly-testing chains omit `master`: that repo builds under a non-release
toolchain, so its root hash differs and a master probe never matches.
-/
def developerContainers (repo : String) : List Container :=
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

/--
How the cache tool is being used, which decides the default lookup chain.

* `developer`: the tool runs on a mathlib4 checkout — the canonical repo, a
  fork, or the nightly-testing repo — by a developer or by CI. Reads follow the
  per-repo trust chain, which may include the developer cache's containers.
* `downstream`: the tool runs in a project that depends on Mathlib. Reads
  default to the public service — a downstream project consumes first-party
  builds, never fork or toolchain-experiment artifacts. The one non-public
  default is a dependency pinned to the nightly-testing repo, which reads
  that repo's own container (see `defaultContainersFor`).
-/
inductive UsageContext where
  | developer
  | downstream
  deriving DecidableEq, Repr, BEq, Inhabited

/--
Resolve the usage context from what the invocation shows.

A checkout with `Mathlib/` at its root (`isMathlibRoot`) is developer use:
mathlib itself, canonical or fork. An explicit `--repo=` also selects developer
use — the user is naming whose cache to read, so the per-repo chain applies
even from a downstream project (a downstream build against a fork commit, say).
Repos other than the canonical one then carry the non-default-scope warning
through the usual `--repo` path.

Everything else is downstream: Mathlib is a dependency, and the read stays on
the public service.
-/
def UsageContext.resolve (isMathlibRoot : Bool) (repoExplicit? : Option String) : UsageContext :=
  if isMathlibRoot || repoExplicit?.isSome then .developer else .downstream

/--
The downstream default lookup chain: public-service containers only. `master`
first, then `legacy` for artifacts predating the write cutover.
-/
def downstreamContainers : List Container := [.master, .legacy]

/--
The downstream chain for a dependency pinned to the nightly-testing repo:
its artifacts exist nowhere else, and the `forks` entry of that repo's
developer chain serves PR flows that downstream builds never take.
-/
def downstreamNightlyContainers : List Container := [.nightlyTesting, .legacy]

/--
Trust-ordered containers to try when downloading, given the usage context.

Developer use keeps the per-repo chain of `developerContainers`, which
reaches into the developer cache for fork and nightly artifacts.

Downstream reads take `downstreamContainers`, with one exception: a project
whose mathlib dependency is the nightly-testing repo (downstream resolution
honors only canonical repos, see `resolveDownstreamRepo`) takes
`downstreamNightlyContainers`. A downstream default never reads fork or
toolchain-experiment artifacts, whatever the repo.
-/
def defaultContainersFor (context : UsageContext) (repo : String) : List Container :=
  match context with
  | .developer => developerContainers repo
  | .downstream =>
    if repo == NIGHTLY_TESTING_REPO then downstreamNightlyContainers
    else downstreamContainers
