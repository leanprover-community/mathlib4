# Cache trust model & security notes

## Background

The mathlib build cache holds CI-built artifacts shared across every
contributor's local checkout. A PR can run arbitrary code during its CI build
(Lean executes user code at elaboration time), so it can write any bytes into
the artifacts that are then packed and uploaded. The infrastructure cannot
validate artifact content; verifying integrity would mean re-running the build,
defeating the point of caching.

The cache thus cannot prevent a malicious build from producing a poisoned
artifact; it prevents delivery of that artifact to a higher-trust consumer.
Artifacts produced at trust level T are only readable by consumers at level T
or below.

## Trust hierarchy and containers

The model spans four storage containers, each written by a distinct class of
CI job and assigned a trust level:

| Container             | Who may write                                          | Trust  | Service  |
|-----------------------|--------------------------------------------------------|--------|----------|
| `master`              | mathlib4 `master`/`staging`, `v4.*` release tags       | high   | public    |
| `forks`               | mathlib4 PR builds, non-master branches, `bors try`    | medium | developer |
| `nightly-testing`     | nightly-testing's trusted branches                     | medium | developer |
| `pr-toolchain-tests`  | nightly-testing's experimental toolchain branches      | low    | developer |

Each writer identity is granted write access to exactly one container, enforced
by the storage backend. An upload aimed at any other container is rejected,
regardless of what the cache binary requests.

The containers are split across two services. The public service (`master`,
plus the read-only `legacy` container) holds only master-trust artifacts; the
developer cache holds every work-in-progress container. The split is
physical: separate storage, separate read endpoints
(`https://cache.mathlib.org` and `https://devcache.mathlib.org`), and
separate write credential flows. A credential for the developer cache's storage cannot
name the public storage at all, so the container isolation for fork-trust
writers is backed by a storage boundary, not only by per-container grants.

On the read side, each consumer has a default lookup chain — the ordered list
of containers it reads from:

| Consumer                | Default lookup chain |
|-------------------------|----------------------|
| mathlib4                | `master`             |
| nightly-testing         | `nightly-testing`, `forks` |
| forks (PRs)             | `master`, `forks`    |
| downstream projects     | `master` (`nightly-testing` for a nightly-pinned dependency) |

The table shows trust classes; every developer chain also ends with the
read-only `legacy` container, elided here. The nightly chain includes `forks`
because PRs from that repo into mathlib4 upload there; it excludes
`pr-toolchain-tests`, so a poisoned upload from an experimental toolchain
branch cannot reach a trusted nightly consumer.

Branches that legitimately need to read their own prior low-trust uploads opt
into a wider chain explicitly.

A downstream project — Mathlib as a dependency — honors only a canonical
detection of its dependency checkout: a fork remote there never steers the
read, so a downstream default never fetches fork or toolchain-experiment
artifacts. The one canonical exception is a dependency pinned to the
nightly-testing repo, which reads that repo's own first-party container (its
artifacts exist nowhere else); the fork container stays out of that chain
too. A downstream user opts into a fork's chain explicitly with `--repo=` or
`--cache-from=`, which carries the usual security notice when it widens the
read.

## Four enforcement layers

The first two enforce the trust boundary; the last two provide correctness
guarantees and additional containment.

### 1. Token-scoped uploads (server-side)

Before uploading, the workflow obtains a short-lived credential for the writer
identity tied to its container. The identity provider issues the credential
only when the workflow's identity — stamped by GitHub from the repo, event
type, and ref — matches a pre-registered grant. The credential's scope is
fixed when it is issued and cannot be widened afterward.

Two flows implement this, one per service. Azure writes mint an OIDC-federated
bearer token whose RBAC role covers exactly one container. Developer-cache
writes exchange the job's GitHub OIDC token at the cache broker for temporary
credentials scoped to one container's namespace inside the developer cache's storage.
That storage holds no public artifacts, so no credential on this
flow can reach what public consumers read.

This is the boundary's anchor: a compromised cache binary, a tampered workflow,
or a malicious PR that captures and replays the credential still cannot upload
outside the one container the credential grants.

### 2. Isolation of the cache binary

The cache binary is built from a trusted branch, never from the PR's checkout,
so the PR's toolchain never reaches the compiler that produces it. Reads and
uploads share one binary on purpose: `put` writes with the same URL
construction `get` reads, so the write path cannot drift from the read
contract. The isolation is the job, not the binary. The binary runs in two
separate jobs — one that fetches and packs artifacts, one that uploads
them — and each job builds its own copy from the trusted source. The PR's own
build writes only its artifacts, which the trusted binary later packs.

The two jobs also run on different runner pools, and the upload token is minted
only in the upload job, so it never reaches the build host; a compromised build
host cannot extract it.

### 3. Read-only source tree during the build

The PR build, where untrusted code runs, executes inside a sandbox that makes
the source tree read-only. This keeps the inputs to the cache key honest while
they are being hashed: without it, a malicious build could rewrite a hash input
(such as the toolchain) between hashing and packing, aligning its keys with a
target branch's and bypassing the partitioning below.

### 4. Hash partitioning

Cache keys derive from the source content, its imports, and the build's
toolchain and configuration. Branches with different toolchains therefore live
in disjoint key spaces, so even within one container their artifacts cannot
collide unless an attacker aligns all of those inputs — which Layer 3 prevents.

This layer is not sufficient alone: it relies on Layer 2 for an honest binary
computing the keys, Layer 3 to keep the inputs honest, and Layer 1 to bound the
damage if partitioning ever fails.

## How CI routes each job

A routing policy decides, for each CI job, which container it writes to and
which lookup chain it reads from. The policy is loaded from the trusted branch,
not from the PR, so a PR cannot route itself to a higher-trust container.

This routing applies only in CI. User machines fall back to the strict per-repo
default and must opt into a wider lookup chain explicitly.

## Per-commit namespace for fork uploads

Within the fork container, uploads are further namespaced by the PR's head
commit. This closes a replay window: artifacts from a closed, hidden, or
force-pushed-away PR live under a different commit, so a later honest PR from
the same fork cannot read them. Uploads to the other containers are not
commit-scoped — each receives uploads from a single trust level, so the
container boundary alone isolates them.

By default a `cache get` reads the fork namespace at the checked-out HEAD: it
can only serve artifacts built from the commit the reader already has, so it
adds no trust over the fork container itself and prints no notice. (CI pins
the same namespace explicitly via `MATHLIB_CACHE_REPO_SCOPE`, set to the build
SHA.) A reader opts into a *different* commit's namespace with
`cache get --scope=SHA`, or lets `cache get --unsafe` discover the most recent
cached fork commits automatically (`--unsafe-window=N` reads the `N` most
recent, default `1`). Either way the reader is choosing to trust whoever
produced those fork artifacts — the per-commit namespace bounds *replay*, not
the trust decision itself — so both forms print the non-default-scope security
notice before reading. Neither runs in CI; CI routing (above) is loaded from
the trusted branch.

## No routing configuration from the working tree

The tool reads no endpoint and no lookup chain from the working tree — there
is no repo-local cache configuration file, and changes must not add one. The
reasons:

The design severs tree-to-tool trust in exactly two places, and both are
load-bearing. In CI, the read-side binary is built from a trusted branch and
run against the PR's tree; the routing rule is that the lookup policy loads
from the trusted branch, never from the PR. A tree-sourced configuration file
would let PR-controlled bytes choose where that trusted binary reads. A read
endpoint serves unverified artifacts that Lean loads, so endpoint choice is
code execution. Downstream, `resolveDownstreamRepo` refuses to let
anything found in the dependency checkout steer the read; a configuration
file inside a transitively pinned mathlib checkout would hand exactly that
steering to whoever authored the pin. A committed file also persists and
propagates in a way an environment variable never does: one merged line
silently redirects every future clone, developer, and CI run of that
repository.

The argument that the lakefile already executes arbitrary code does not
change this: that equivalence holds only for a user who deliberately builds
an untrusted branch, and fails for the two consumers above, who never opted
in.

The supported way to give a project a default endpoint is to commit the
*environment*, not tool configuration: a `direnv` `.envrc` (guarded by
direnv's own per-machine `direnv allow`) or a CI variable, setting
`MATHLIB_CACHE_GET_URL`. The environment is invoker-owned and per-invocation;
the tree never names an endpoint.

## Explicitly out of scope

The trust model does not attempt to defend against:

- **Compromised upstream Lean releases** — a malicious toolchain on the trusted
  branch builds the cache binary itself.
- **Compromised storage tenant** — admin-level compromise defeats the access
  grants.
- **Substituted read endpoint** — the cache does not verify downloaded bytes, so
  whichever host answers a read carries the storage tenant's trust. Those are
  the default read hosts `https://cache.mathlib.org` and
  `https://devcache.mathlib.org`, or a host named by
  `MATHLIB_CACHE_GET_URL` / `MATHLIB_CACHE_BASE_URL` /
  `MATHLIB_CACHE_DEVELOPER_BASE_URL`.
- **Sandbox escape via kernel vulnerability** — invalidates Layer 3.
- **Maintainer trust on the trusted branches** — write access to a branch the
  cache binary is built from can land a bad tool, workflow, or toolchain.
- **Compromised CI platform credentials** — forged identity tokens break the
  upload boundary.
- **Validation of artifact byte-identity** — the cache key identifies inputs,
  not bytes; containment is trust-bounded delivery, not fetch-time detection.

## Code pointers

| Concern                                        | File(s)                                                          |
|------------------------------------------------|------------------------------------------------------------------|
| Container model, service split, URL shape, per-repo and per-context defaults | [`Cache/Infra.lean`](Infra.lean) (`Container.service`, `UsageContext`, `defaultContainersFor`) |
| Read-fallback resolution, dispatch             | [`Cache/Requests.lean`](Requests.lean) (`effectiveGetURLs`)      |
| Upload destination, credentials, and engines   | [`Cache/Upload.lean`](Upload.lean) (`stagedUploadDest`, `uploadAuthFrom`) |
| Trust property tests                           | [`Cache/Test.lean`](Test.lean)                                   |
| Repository-placement policy (tool vs CI blocks vs services) | `docs/developer-cache-split.md` in `mathlib-initiative/cache-infrastructure` |
| User-facing CLI surface, env vars              | [`Cache/Main.lean`](Main.lean), [`Cache/README.md`](README.md)   |
| OIDC mint + per-job dispatch                   | [`.github/workflows/build_template.yml`](../.github/workflows/build_template.yml) (`upload_cache` job) |
| (repo, ref) → trust class policy table         | [`.github/actions/cache-trust-dispatch/action.yml`](../.github/actions/cache-trust-dispatch/action.yml) |
| Caller `cache_application_id` wiring           | [`.github/workflows/build.yml`](../.github/workflows/build.yml), [`bors.yml`](../.github/workflows/bors.yml), [`build_fork.yml`](../.github/workflows/build_fork.yml), [`ci_dev.yml`](../.github/workflows/ci_dev.yml), [`release_cache.yml`](../.github/workflows/release_cache.yml) |
