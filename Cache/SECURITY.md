# Cache trust model & security notes

> **If you change the trust model** — container assignments, Azure RBAC, the
> `cache-trust-dispatch` policy table, or the OIDC federation subjects on any
> writer — **update this file in the same PR.** This document is the canonical
> implementation-level reference for how the cache stays trust-bounded; if it
> drifts from reality, future maintainers won't be able to audit the design.

## Why this exists

The mathlib build cache holds CI-built `.olean` artifacts that are shared
across every contributor's local checkout. Anyone can submit a PR that, during
its CI build, runs arbitrary Lean code (`#eval`, `initialize` blocks, macros
all elaborate during compilation). That code can write any bytes it wants to
the `.olean` files in the build directory, which the cache tool then packs
and uploads. The cache infrastructure cannot validate `.olean` content —
verifying "is this artifact honest?" would require re-running the build,
defeating the point of caching.

So the cache cannot prevent a malicious build from *producing* a poisoned
artifact. What it does prevent is that artifact being *served to a
higher-trust consumer*. The system is built around **trust-bounded delivery**:
artifacts produced by a CI job at trust level T are only ever readable by
consumers at level T or below.

## Trust hierarchy and containers

Five containers on the `lakecache` Azure Blob Storage account, each fed by a
dedicated CI-job class:

| Container                          | Writer (Entra app)                              | OIDC subject pattern (GitHub ref)                            | Trust |
|------------------------------------|-------------------------------------------------|--------------------------------------------------------------|-------|
| `mathlib4-master`                  | "Mathlib CI Cache Writer - Master"              | `mathlib4`: `refs/heads/master`, `staging`                   | high  |
| `mathlib4-forks`                   | "Mathlib CI Cache Writer - Non-Master"          | `mathlib4`: `pull_request` and `refs/heads/*` (wildcard)     | medium |
| `mathlib4-nightly-testing`         | "Mathlib CI Cache Writer - Nightly Testing"     | `mathlib4-nightly-testing`: `refs/heads/{nightly-testing, nightly-testing-green}` + `refs/heads/bump/*` wildcard | medium |
| `mathlib4-pr-toolchain-tests`      | "Mathlib CI Cache Writer - PR Toolchain Tests"  | `mathlib4-nightly-testing`: `refs/heads/*` wildcard          | low |
| `mathlib4` (legacy)                | Master writer only                              | n/a — populated by the master writer alongside `mathlib4-master` | mixed |

Writer-to-container mapping is enforced at the Azure side via per-container
`Storage Blob Data Contributor` RBAC grants. A workflow whose
`cache_application_id` selects a given writer cannot upload to a container
that writer isn't granted on — Azure 403s the PUT, no matter what the cache
binary tries.

The `legacy` container exists as a cross-version read fallback. The master
writer publishes to it alongside `mathlib4-master`, which lets cache binaries
that don't know about the per-trust-level containers (e.g. a downstream Lean
project pinning an older mathlib commit, or any other consumer with a bare
`mathlib4` URL) find master-built artifacts at the historical location.

Read-side fallback chains, mapped by repo (see `Cache/Infra.lean:defaultContainersForRepo`):

| GitHub repo                                     | Default container chain          |
|-------------------------------------------------|----------------------------------|
| `leanprover-community/mathlib4`                 | `master`, `legacy`               |
| `leanprover-community/mathlib4-nightly-testing` | `nightly-testing`, `legacy`      |
| any fork (PRs)                                  | `forks`, `legacy`                |

The trusted-nightly default deliberately excludes `pr-toolchain-tests`, so a
poisoned upload from `lean-pr-testing-*` cannot silently reach a
`nightly-testing-green` consumer. Branches that legitimately need a wider
chain — toolchain-test branches reading their own previous uploads — opt in
via `MATHLIB_CACHE_FROM`, set by `cache-trust-dispatch` (see *CI dispatch*
below).

## Four enforcement layers

Listed in order of strength. The first two are the actual trust boundary; the
last two are correctness and defense-in-depth.

### 1. OIDC + Azure RBAC (server-side, immutable from inside any workflow)

The workflow mints a short-lived bearer token via GitHub OIDC for a specific
Entra app (`cache_application_id`). Entra issues the token only if the GitHub
OIDC `subject` claim — which GitHub itself stamps based on `repo` + event
type + ref — matches a federated credential on that app. The token's RBAC
scope is fixed at mint time and cannot be widened by anything the cache
binary does.

A compromised cache binary, a tampered workflow YAML hard-coding
`--container=master`, or a malicious PR's `#eval` exfiltrating-and-reusing
the token — none of those escalate beyond what the token's container grant
allows.

Implementation: `.github/workflows/build_template.yml` (the
*Azure CLI OIDC login and mint storage bearer token* step), and the Entra
federation set up by `scripts/setup_cache_entra.sh`.

### 2. `tools_branch` isolation of the cache binary

The cache binary is compiled in a separate job and runner from a trusted
branch (`master` on canonical mathlib4, `nightly-testing-green` on the
nightly-testing repo). It is **not** built from the PR's checkout, so the
PR's `lean-toolchain` never reaches the compiler that produces the cache
binary. The PR build's `lake build` (in landrun, see below) writes only to
its own runner's `pr-branch/.lake/`; the cache binary's location is on a
different ephemeral runner entirely (the `upload_cache` job).

Implementation: `.github/workflows/build_template.yml` — the
*Checkout tools branch* + *build cache executable* steps in the
`upload_cache` job, plus the `tools-branch` checkout in the `build` job used
for read-side `cache get`.

### 3. landrun read-only source tree

The `lake build` step (where PR code's elaboration actually runs) executes
under landrun with `--rox /home/lean/actions-runner/_work`, making the entire
PR source tree read-only. This is what enforces that the root-hash inputs
(`lakefile.lean`, `lean-toolchain`, `lake-manifest.json`, the source files
themselves) remain honest at hash-computation time. Without this, a
malicious compiler could rewrite `lean-toolchain` between build and pack,
aligning its hash space with a target branch's and bypassing hash
partitioning entirely.

The `cache stage` step has a similarly restrictive landrun config (no
`--unrestricted-network`, source still read-only).

Implementation: `.github/workflows/build_template.yml` — the `shell:`
defaults on the build job, and the explicit landrun shells on the stage
steps.

### 4. Hash partitioning (defense in depth)

Cache keys are derived from source content + imports + a root hash that
includes `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` content
(see `Cache/Hashing.lean:getRootHash`). Branches with different toolchains
live in disjoint hash spaces, so even within the same container, blobs at
different keys cannot collide unless an attacker can align all root-hash
inputs. With Layer 3 in place, an attacker cannot modify those inputs
between elaboration and pack time, so this layer holds.

This layer is *not* load-bearing on its own — it depends on Layer 3 to keep
the inputs honest, and on Layer 1 to bound damage if it ever fails. It is
listed last because it should never be the only thing between you and an
attack.

## CI dispatch: how (repo, branch) gets routed

The composite action at `.github/actions/cache-trust-dispatch/action.yml` is
the single source of truth for "which container + which OIDC writer + which
read chain corresponds to this job context". It is invoked by all three
trust-aware jobs:

- **build** — needs `MATHLIB_CACHE_FROM` so pre-build cache gets find what a
  prior run on this same branch uploaded.
- **upload_cache** — needs `MATHLIB_CACHE_PRIMARY` to choose the container
  for `put-staged`.
- **post_steps** — needs `MATHLIB_CACHE_FROM` to verify the roundtrip by
  reading back this CI run's just-uploaded artifacts.

The dispatch is loaded from master / tools-branch — PR-supplied workflow
files never override it.

User machines deliberately do **not** apply this dispatch: a maintainer
running `lake exe cache get` locally on a `lean-pr-testing-*` checkout uses
the strict per-repo default and must explicitly opt into widening with
`--cache-from` or `MATHLIB_CACHE_FROM=…`. This is the *CI-only trust policy
in YAML; user-machine logic in Lean* principle: explicit, auditable trust
choices on the runners that hold the credentials, conservative defaults
everywhere else.

## Per-commit namespace for fork-trust uploads

Fork-trust uploads (anything dispatched to `mathlib4-forks`) are namespaced
not only by repo but also by the head commit SHA: paths take the shape
`/f/{repo}/{sha}/{hash}.ltar`. The SHA is sourced from
`github.event.pull_request.head.sha || github.sha` in
`cache-trust-dispatch`, propagated to the cache binary via the
`MATHLIB_CACHE_REPO_SCOPE` environment variable, and applied in
`Cache/Requests.lean:mkFileURL` only when the resulting path is prefixed
(flat paths in `master`/`legacy×MATHLIBREPO` are unaffected).

This isolates each commit's CI run into its own namespace, which closes
the within-fork temporal replay window: artifacts uploaded by a closed,
hidden, or force-pushed-away PR cannot be read by a later honest PR from
the same fork, because their head SHAs differ. The `--repo` segment is
kept alongside `--scope` as an audit/discoverability handle (it lets you
list all of a given fork's uploads in one place), not as a security
layer; the per-SHA segment is the actual isolation primitive.

`master`, `nightly-testing`, and `pr-toolchain-tests` uploads are *not*
SHA-scoped. Master has a single writer so within-trust replay is moot;
the other two are kept simpler at the per-trust-level isolation that
their dedicated containers already provide.

## URL shaping (why containers, not repos, decide flat vs prefixed)

`Cache/Infra.lean:Container.flatPath` determines whether artifacts in a
given container are stored at `/f/{hash}.ltar` (flat) or
`/f/{repo}/{hash}.ltar` (prefixed):

- `master` — always flat. The master writer is the only writer; no
  collision risk.
- `legacy` — flat for `MATHLIBREPO`, prefixed otherwise. The hybrid behavior
  preserves the path scheme that bare-`mathlib4` readers expect for both
  canonical-mathlib4 artifacts and fork-attributed artifacts.
- `forks`, `nightly-testing`, `pr-toolchain-tests` — always prefixed. These
  hold artifacts from multiple writer contexts (including canonical-repo
  builds whose trust is fork-equivalent, like `ci-dev/*`); a flat layout
  would let two writers collide at identical hashes.

Making URL shape a property of the container, not the repo, ensures every
write inside a multi-writer container is namespaced — including the case of
a canonical-mathlib4 ref dispatched to the `forks` container (its uploads
end up at `/f/leanprover-community/mathlib4/…`, prefixed alongside every
other fork's prefix, not flat where they'd shadow the master-uploaded path
scheme inside the wrong container).

## Cache uploads on user machines

If neither `--container` nor `MATHLIB_CACHE_PUT_URL` is set, `cache put`
uploads to the `legacy` container with a deprecation warning to stderr. CI
workflows pass `--container=NAME` explicitly via `cache-trust-dispatch`; user
machines invoking `cache put` are required to make the choice consciously.
There is no implicit dispatch that routes a non-CI invocation into a
trusted container.

## Explicitly out of scope

The trust model does not attempt to defend against:

- **Compromised upstream Lean releases.** If the `lean-toolchain` text on
  master ever resolves to a malicious compiler — whether via supply-chain
  attack on `leanprover/lean4` releases or a maintainer-merged toolchain
  bump to a bad ref — that compiler builds the cache binary itself. Defense
  lives upstream of mathlib (Lean release process integrity, branch
  protection on master).
- **Compromised Azure tenant.** If the Azure subscription / Entra tenant is
  compromised at the admin level, RBAC means nothing.
- **Sandbox escape via Linux kernel vulnerability.** landrun is a
  Landlock-based sandbox; a kernel bug allowing escape would invalidate
  Layer 3. Mitigation is OS-level patching on the runner hosts.
- **Maintainer trust integrity on canonical mathlib4 master.** Anyone with
  write access to mathlib4's master branch (and therefore the `tools_branch`
  checkout used by master CI) can land a bad change to the cache tool,
  workflow files, or `lean-toolchain`. Defense is code review and branch
  protection.
- **Maintainer trust integrity on `mathlib4-nightly-testing`**, especially
  on `nightly-testing-green`, which serves as the `tools_branch` source for
  nightly CI. Should be protected at the same level as master.
- **Compromised GitHub Actions platform credentials.** If GitHub itself
  issues forged OIDC tokens, the federation boundary breaks.
- **Validation of artifact byte-identity.** The cache key answers "what
  inputs should have produced this," not "what exact bytes are inside." A
  malicious build at hash H produces a poisoned artifact at hash H; the
  damage is contained by trust-bounding *where* that artifact can be
  delivered, not by detecting the poisoning at fetch time.

## Code pointers

| Concern                                        | File(s)                                                          |
|------------------------------------------------|------------------------------------------------------------------|
| Container model, URL shape, per-repo defaults  | `Cache/Infra.lean`                                               |
| Read-fallback resolution, upload URL, dispatch | `Cache/Requests.lean` (`effectiveGetURLs`, `effectiveUploadURL`) |
| Trust property tests                           | `Cache/Test.lean`                                                |
| User-facing CLI surface, env vars              | `Cache/Main.lean`, `Cache/README.md`                             |
| OIDC mint + per-job dispatch                   | `.github/workflows/build_template.yml` (`upload_cache` job)      |
| (repo, branch) → trust class policy table      | `.github/actions/cache-trust-dispatch/action.yml`                |
| Caller `cache_application_id` ternaries        | `.github/workflows/build.yml`, `bors.yml`, `build_fork.yml`, `ci_dev.yml` |
| Azure-side provisioning                        | `scripts/setup_cache_azure.sh`, `setup_cache_entra.sh`, `setup_cache_rbac.sh` |
