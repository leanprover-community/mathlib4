/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch, Arthur Paulino
-/

import Cache.Env

/-!
# Cache backend infrastructure

The multi-container model: the trust-classified containers, their layouts,
and the read base rule, together with the GitHub repo names the cache tool
dispatches on.

This lives apart from `Cache.Requests` so the container model stands on its
own, independent of the HTTP/curl machinery that consumes it. Which
containers a read tries, and from which host, is the workflow's decision
(`Cache.Workflow`).
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
not a particular storage technology: each host that serves the contract
resolves it to its own backend. The Azure Blob Storage account
(`lakecache`) serves the same namespaces as its own containers, which is what
the legacy switch addresses directly. A CI job at a given trust level may
write only to its corresponding container, and a chain read tries the most
trusted container first.
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

/-- All known containers, listed in their canonical declaration order. -/
def all : List Container :=
  [.master, .forks, .nightlyTesting, .prToolchainTests]

/-- Parse a short name back into a `Container`: the inverse of `name` over
`all`, so the three stay in agreement by construction. Matching is
case-insensitive. -/
def parse? (s : String) : Option Container :=
  all.find? (·.name == s.toLower)

/--
The container's segment in the URL contract: read URLs are
`{base}/{pathSegment}/{key}`, and a bucket backend uses the same string as its
key prefix. The segment is also the Azure storage container name on the
`lakecache` account; `Container.azureURL` builds its URL from it.

Every container follows the `mathlib4-{name}` convention.
-/
def pathSegment (c : Container) : String :=
  s!"mathlib4-{c.name}"

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
- `forks`, `nightly-testing`, and `pr-toolchain-tests` always namespace by
  repo. They collect artifacts from many writers — different forks, different
  toolchain refs, and canonical-repo builds whose trust is fork-equivalent
  (`ci-dev/*`, `bors trying`) — so identical hashes from different writers must
  stay on distinct paths.
-/
def flatPath : Container → Bool
  | .master => true
  | _ => false

/--
Whether the container holds per-commit namespaces, `/f/{repo}/{sha}/...`,
which a scope addresses. Only `forks` does: each fork PR build uploads under
its head commit, so one commit's artifacts never serve another commit on the
same fork (see `SECURITY.md`). A read of the other containers is unscoped.
-/
def perCommit : Container → Bool
  | .forks => true
  | _ => false

end Container

/--
Blob path of the directory that holds the cache artifacts, per the container's
layout policy (`Container.flatPath`): `f` for a flat container, `f/{repo}` for
a repo-namespaced one, `f/{repo}/{scope}` when a per-SHA scope applies. A
`none` container stands for a flat endpoint, such as `MATHLIB_CACHE_GET_URL`,
and gives `f`. `repo` is lowercased via `normalizeRepo`. A file lives at
`{fileDirPath container repo scope}/{fileName}`; `mkFileURL` and
`containerUploadDest` both build on this, so reads and uploads share one path
contract. Like `markerDirPath` (`Cache/Marker.lean`), the path carries no
trailing slash.
-/
def fileDirPath (container : Option Container) (repo : String)
    (repoScope : Option String) : String :=
  let repo := normalizeRepo repo
  if container.all (·.flatPath) then "f"
  else match repoScope with
    | some s => s!"f/{repo}/{s}"
    | none => s!"f/{repo}"

/--
The public Mathlib cache endpoint, the cache resolver. It serves the
`/{container}/{key}` namespace of every container and caches artifacts at its
edge, so reads cost the project less and land nearer the reader.
-/
def publicCacheEndpoint : String := "https://cache.mathlib.org"

/--
The read base of a workflow whose own host is `endpoint`:
`MATHLIB_CACHE_BASE_URL` (`baseEnv?`) when set, else the Azure storage account
when `useLegacy` (`MATHLIB_CACHE_DEBUG_USE_LEGACY`, a troubleshooting
fallback) is set, else `endpoint`. `normalizeBaseURL` reads the
variable, so it arrives trimmed, free of trailing slashes, and unset when
empty.

A read URL is `{base}/{pathSegment}/{key}`, the one namespace shape every host
serves, so a host that mirrors the whole namespace is a valid base for every
container, and the Azure account holds every container. This override differs
from `MATHLIB_CACHE_GET_URL`. That variable serves external consumers: it
names one flat endpoint and bypasses the container lookup chain.
`MATHLIB_CACHE_BASE_URL` serves mathlib's own consumers, that is, CI and
contributors to the repository. It keeps the lookup chain and rebases each
container read under the given host.

Only reads follow this base. Uploads and marker writes go under the
container's root, the Azure account or `MATHLIB_CACHE_PUT_URL`
(`stagedUploadDestFrom`).
-/
def readBaseFrom (endpoint : String) (baseEnv? : Option String) (useLegacy : Bool) : String :=
  (normalizeBaseURL baseEnv?).getD (if useLegacy then azureAccountURL else endpoint)

/-- `readBaseFrom` under the settings `s`. -/
def readBase (s : Settings) (endpoint : String) : String :=
  readBaseFrom endpoint s.baseURL? s.useLegacy

/-- The read URL of container `c` for a workflow whose own host is
`endpoint`, under the settings `s`: `{readBase s endpoint}/{pathSegment}`. -/
def Container.readURL (c : Container) (s : Settings) (endpoint : String) : String :=
  s!"{readBase s endpoint}/{c.pathSegment}"

/--
Comma-separated list parser for `--cache-from=a,b,c`.

Returns `none` if any element is unrecognized.
-/
def parseCacheFromList (s : String) : Option (List Container) := do
  let parts := s.splitOn ","
  parts.mapM (fun p => Container.parse? p.trimAscii.toString)
