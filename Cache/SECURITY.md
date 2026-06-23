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

| Container             | Who may write                                          | Trust  |
|-----------------------|--------------------------------------------------------|--------|
| `master`              | mathlib4 `master`/`staging`                            | high   |
| `forks`               | mathlib4 PR builds, non-master branches, `bors try`    | medium |
| `nightly-testing`     | nightly-testing's trusted branches                     | medium |
| `pr-toolchain-tests`  | nightly-testing's experimental toolchain branches      | low    |

Each writer identity is granted write access to exactly one container, enforced
by the storage backend. An upload aimed at any other container is rejected,
regardless of what the cache binary requests.

On the read side, each repo has a default lookup chain — the ordered list of
containers a consumer reads from:

| Consumer                | Default lookup chain |
|-------------------------|----------------------|
| mathlib4                | `master`             |
| nightly-testing         | `nightly-testing`    |
| forks (PRs)             | `master`, `forks`    |

The nightly default excludes the low-trust container, so a poisoned upload from
an experimental toolchain branch cannot reach a trusted nightly consumer.
Branches that legitimately need to read their own prior low-trust uploads opt
into a wider chain explicitly.

## Four enforcement layers

The first two enforce the trust boundary; the last two provide correctness
guarantees and additional containment.

### 1. Token-scoped uploads (server-side)

Before uploading, the workflow obtains a short-lived token for the writer
identity tied to its container. The identity provider issues the token only
when the workflow's identity — stamped by GitHub from the repo, event type, and
ref — matches a pre-registered credential. The token's scope is fixed when it
is issued and cannot be widened afterward.

This is the boundary's anchor: a compromised cache binary, a tampered workflow,
or a malicious PR that captures and replays the token still cannot upload
outside the one container the token grants.

### 2. Isolation of the cache binary

The cache binary is built from a trusted branch, never from the PR's checkout,
so the PR's toolchain never reaches the compiler that produces it. The binary
runs in two separate jobs — one that fetches and packs artifacts, and one that
uploads them — and each builds its own copy from the trusted source. The PR's
own build writes only its artifacts, which the trusted binary later packs.

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

## Explicitly out of scope

The trust model does not attempt to defend against:

- **Compromised upstream Lean releases** — a malicious toolchain on the trusted
  branch builds the cache binary itself.
- **Compromised storage tenant** — admin-level compromise defeats the access
  grants.
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
| Container model, URL shape, per-repo defaults  | [`Cache/Infra.lean`](Infra.lean)                                 |
| Read-fallback resolution, upload URL, dispatch | [`Cache/Requests.lean`](Requests.lean) (`effectiveGetURLs`, `effectiveUploadURL`) |
| Trust property tests                           | [`Cache/Test.lean`](Test.lean)                                   |
| User-facing CLI surface, env vars              | [`Cache/Main.lean`](Main.lean), [`Cache/README.md`](README.md)   |
| OIDC mint + per-job dispatch                   | [`.github/workflows/build_template.yml`](../.github/workflows/build_template.yml) (`upload_cache` job) |
| (repo, branch) → trust class policy table      | [`.github/actions/cache-trust-dispatch/action.yml`](../.github/actions/cache-trust-dispatch/action.yml) |
| Caller `cache_application_id` ternaries        | [`.github/workflows/build.yml`](../.github/workflows/build.yml), [`bors.yml`](../.github/workflows/bors.yml), [`build_fork.yml`](../.github/workflows/build_fork.yml), [`ci_dev.yml`](../.github/workflows/ci_dev.yml) |
