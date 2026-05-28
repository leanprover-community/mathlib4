/-
Copyright (c) 2023 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino
-/

/-!
# Cache backend infrastructure

The multi-container model (trust-classified Azure containers + per-repo
allowlist) and the canonical GitHub repo names the cache tool dispatches on.

Kept separate from `Cache.Requests` so changes to the container model or
trust ordering don't drag the HTTP/curl machinery into review.
-/

namespace Cache.Requests

open System (FilePath)

/-- The full name of the main Mathlib GitHub repository. -/
def MATHLIBREPO := "leanprover-community/mathlib4"

/-- The full name of the Mathlib nightly-testing GitHub repository. -/
def NIGHTLY_TESTING_REPO := "leanprover-community/mathlib4-nightly-testing"

/--
Trust-classified Azure storage containers for the Mathlib cache.

Each variant maps to one Azure Blob Storage container on the `lakecache` storage
account. The intent is that a CI job at a given trust level may only write to
its corresponding container, and that `cache get` always tries the most trusted
container first.
-/
inductive Container where
  /-- The new most-trusted container (`mathlib4-master`) — only master CI is
  permitted to write here. -/
  | master
  /-- Container for PR builds on forks of mathlib4. -/
  | forks
  /-- Container for the `nightly-testing` branch and related refs. -/
  | nightlyTesting
  /-- Container for toolchain-PR test runs. -/
  | prToolchainTests
  /-- The legacy bare `mathlib4` container, kept as a last-resort read
  fallback during the migration to per-trust-level containers. Historically
  every CI wrote here, so it still holds the bulk of in-flight artifacts.

  During the migration, **only master CI** dual-writes to `legacy` alongside
  its `mathlib4-master` upload — so consumers running older cache tools
  (which only know how to read from `mathlib4`) keep finding master-built
  artifacts. Forks and nightly-testing deliberately do *not* dual-write
  here: allowing low-trust writers into the bucket that old readers depend
  on would re-introduce the cross-trust poisoning vector this split exists
  to eliminate. Writes can be cut entirely once all consumers read from
  the dedicated containers. -/
  | legacy
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

/-- Parse a short name back into a `Container`. -/
def parse? : String → Option Container
  | "master"             => some .master
  | "forks"              => some .forks
  | "nightly-testing"    => some .nightlyTesting
  | "pr-toolchain-tests" => some .prToolchainTests
  | "legacy"             => some .legacy
  | _                    => none

/--
Azure storage container name on the `lakecache` storage account.

Per-trust-level containers follow the `mathlib4-{name}` convention. The
`legacy` case is the bare `mathlib4` container kept as a migration fallback.
-/
def azureContainerName : Container → String
  | .legacy => "mathlib4"
  | c       => s!"mathlib4-{c.name}"

/-- Public Azure Blob Storage base URL for a container. -/
def azureURL (c : Container) : String :=
  s!"https://lakecache.blob.core.windows.net/{c.azureContainerName}"

/--
Whether file lookups in this container use the flat `/f/<hash>` layout for
the given `repo`, or namespace under `/f/<repo>/<hash>`.

The decision is *per container*, not per repo: a single container can be fed
by several writers whose `repo` argument doesn't always match the trust
implied by the container, and a stable layout per container is what keeps
readers and writers in sync.

- `master` is canonical-only — only trusted master CI is admitted by RBAC,
  and those writes always carry `repo == MATHLIBREPO`. The layout is flat.
- `legacy` is the historical monolithic `mathlib4` container. It encoded the
  writer's trust in the path: canonical-repo writers landed at `/f/<hash>`
  (where older mathlib4 readers still expect to find them), fork writers
  landed at `/f/<repo>/<hash>`. We preserve that mixed behavior for
  back-compat with consumers that still read from the bare container.
- Every other per-trust-level container (`forks`, `nightly-testing`,
  `pr-toolchain-tests`) always namespaces by repo. These hold artifacts
  from multiple writers — different forks, different toolchain refs, plus
  canonical-repo builds whose trust level is fork-equivalent (e.g.
  `ci-dev/*` and `bors trying` on the canonical repo, both of which dispatch
  to the `forks` container). A flat layout there would collide on identical
  hashes from different writers, and the container alone doesn't disambiguate.
-/
def flatPath (c : Container) (repo : String) : Bool :=
  match c with
  | .master => true
  | .legacy => repo == MATHLIBREPO
  | _ => false

end Container

/--
Comma-separated list parser for `--cache-from=a,b,c`.

Returns `none` if any element is unrecognized.
-/
def parseCacheFromList (s : String) : Option (List Container) := do
  let parts := s.splitOn ","
  parts.mapM (fun p => Container.parse? p.trimAscii.toString)

/--
Default trust-ordered list of containers to try when downloading for a given
GitHub repo. Each repo maps to its own dedicated, trust-classified container,
with the `legacy` bare-`mathlib4` container appended as a universal
last-resort fallback during the migration.

We deliberately do NOT include the new `master` container in the fallback
list for non-master repos: `master` only stores canonical mathlib4 paths
(`/f/{hash}.ltar`) and never fork-prefixed paths, so a lookup there from a
fork iteration would always 404. (Fork PRs still get to read master-built
artifacts via the *outer* repo loop, where the iteration with
`repo = MATHLIBREPO` uses the canonical path scheme.)
-/
def defaultContainersForRepo (repo : String) : List Container :=
  if repo == MATHLIBREPO then
    [.master, .legacy]
  else if repo == NIGHTLY_TESTING_REPO then
    -- Strict default for the nightly-testing repo: `nightly-testing` + `legacy`.
    -- **`pr-toolchain-tests` is deliberately NOT in this default** — trusted-
    -- nightly consumers (`nightly-testing`, `nightly-testing-green`, `bump/*`)
    -- must not silently fall back to artifacts uploaded by low-trust
    -- toolchain-PR test branches.
    --
    -- Toolchain-PR test branches (`lean-pr-testing-*`, `batteries-pr-testing-*`)
    -- need to read their own previously-uploaded artifacts from
    -- `pr-toolchain-tests`. That widening is CI-only and lives in the workflow
    -- (`build_template.yml` exports `MATHLIB_CACHE_FROM=pr-toolchain-tests,
    -- nightly-testing,legacy` for those refs). On a user machine, a maintainer
    -- working locally on `lean-pr-testing-*` can opt in with `--cache-from=...`
    -- — auto-widening locally would silently subject every consumer to the
    -- least-trusted container.
    [.nightlyTesting, .legacy]
  else
    -- Fork repos (PRs) and anything else: master first (it holds the bulk
    -- of any fork build's deps, and is the highest-trust source), then the
    -- fork's own container for PR-specific files, then legacy as the
    -- migration tail. `legacy` is transitional and will be dropped once
    -- master CI's dual-write to it is retired, leaving `[master, forks]`.
    --
    -- Note: master is NOT in the nightly-testing chain above — that repo
    -- runs under a non-release toolchain, so the root hash differs from
    -- master's and master probes would always 404.
    [.master, .forks, .legacy]
