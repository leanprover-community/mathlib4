# Cache trust model & security notes

## Background

The mathlib build cache holds CI-built `.olean` artifacts that are shared
across every contributor's local checkout. Anyone can submit a PR that, during
its CI build, runs arbitrary Lean code (`#eval`, `initialize` blocks, macros
all elaborate during compilation). That code can write any bytes it wants to
the `.olean` files in the build directory, which the cache tool then packs
and uploads. The cache infrastructure cannot validate `.olean` content;
verifying artifact integrity would require re-running the build, defeating
the point of caching.

The cache therefore cannot prevent a malicious build from producing a
poisoned artifact. What it prevents is delivery of that artifact to a
higher-trust consumer. The design enforces trust-bounded delivery:
artifacts produced by a CI job at trust level T are only readable by
consumers at level T or below.

## Trust hierarchy and containers

Four containers on the `lakecache` Azure Blob Storage account, each fed by a
dedicated CI-job class:

| Container                          | Writer (Entra app)                              | Branches that may write                                                    | Trust  |
|------------------------------------|-------------------------------------------------|----------------------------------------------------------------------------|--------|
| `mathlib4-master`                  | "Mathlib CI Cache Writer - Master"              | mathlib4: `master` and `staging`                                           | high   |
| `mathlib4-forks`                   | "Mathlib CI Cache Writer - Non-Master"          | mathlib4: PR builds (from forks), non-master branches, and `bors try`      | medium |
| `mathlib4-nightly-testing`         | "Mathlib CI Cache Writer - Nightly Testing"     | nightly-testing repo: `nightly-testing`, `nightly-testing-green`, `bump/*` | medium |
| `mathlib4-pr-toolchain-tests`      | "Mathlib CI Cache Writer - PR Toolchain Tests"  | nightly-testing repo: any other branch (e.g. `lean-pr-testing-*`)          | low    |

Writer-to-container mapping is enforced at the Azure side via per-container
`Storage Blob Data Contributor` RBAC grants. A workflow whose
`cache_application_id` selects a given writer cannot upload to a container
that writer isn't granted on; Azure returns 403 on the PUT regardless of
what the cache binary requests.

Read-side fallback chains, mapped by repo (see `Cache/Infra.lean:defaultContainersForRepo`):

| GitHub repo                                     | Default container chain |
|-------------------------------------------------|-------------------------|
| `leanprover-community/mathlib4`                 | `master`                |
| `leanprover-community/mathlib4-nightly-testing` | `nightly-testing`       |
| any fork (PRs)                                  | `forks`                 |

The trusted-nightly default excludes `pr-toolchain-tests` so that a
poisoned upload from `lean-pr-testing-*` cannot silently reach a
`nightly-testing-green` consumer. Branches that need a wider chain
(toolchain-test branches reading their own previous uploads) opt in via
`MATHLIB_CACHE_FROM`, set by `cache-trust-dispatch` (see *CI dispatch*
below).

## Four enforcement layers

The first two enforce the trust boundary; the last two provide correctness
guarantees and additional containment.

### 1. OIDC + Azure RBAC (server-side, immutable from inside any workflow)

The workflow mints a short-lived bearer token via GitHub OIDC for a specific
Entra app (`cache_application_id`). Entra issues the token only if the GitHub
OIDC `subject` claim — which GitHub itself stamps based on `repo` + event
type + ref — matches a federated credential on that app. The token's RBAC
scope is fixed at mint time and cannot be widened by anything the cache
binary does.

None of the following can escalate beyond what the token's container
grant allows: a compromised cache binary, a tampered workflow YAML
hard-coding `--container=master`, or a malicious PR's `#eval`
exfiltrating and reusing the token.

Implementation: `.github/workflows/build_template.yml` (the
*Azure CLI OIDC login and mint storage bearer token* step). The Entra
federation between GitHub OIDC subjects and the writer apps is configured
on the Entra side.

### 2. `tools_branch` isolation of the cache binary

The cache binary is compiled from a trusted branch (`master` on canonical
mathlib4, `nightly-testing-green` on the nightly-testing repo), never
from the PR's checkout — the PR's `lean-toolchain` never reaches the
compiler that produces the cache binary. The binary runs in two jobs:

- `build` runs `cache get` (pre-build, to populate `.lake/build` from
  remote artifacts) and `cache stage` (post-build, to pack the freshly
  built `.olean` files into `.ltar` archives staged for upload).
- `upload_cache` runs `cache put-staged` to PUT those staged archives to
  Azure.

Each job checks out tools-branch independently and builds its own copy of
the cache binary from that source. The PR's `lake build` (in landrun,
see below) writes only to its own runner's `pr-branch/.lake/`, where the
cache binary later picks up the `.olean` outputs for packing.

The two jobs also run on different runner pools: `build` uses self-hosted
runners (the Hoskinson pool), while `upload_cache` runs on GitHub-hosted
ephemeral runners. The OIDC bearer token is minted inside `upload_cache`
and never enters the build runner, so a rooted self-hosted host cannot
extract it.

Implementation: `.github/workflows/build_template.yml` — the
*Checkout tools branch* + *build cache executable* steps in both the
`build` and `upload_cache` jobs.

### 3. landrun read-only source tree

The `lake build` step, where PR code's elaboration runs, executes under
landrun with `--rox /home/lean/actions-runner/_work`, making the entire PR
source tree read-only. This keeps the root-hash inputs (`lakefile.lean`,
`lean-toolchain`, `lake-manifest.json`, and the source files themselves)
honest at hash-computation time. Without it, a malicious compiler could
rewrite `lean-toolchain` between build and pack, aligning its hash space
with a target branch's and bypassing hash partitioning entirely.

The `cache stage` step has a similarly restrictive landrun config (no
`--unrestricted-network`, source still read-only).

Implementation: `.github/workflows/build_template.yml` — the `shell:`
defaults on the build job, and the explicit landrun shells on the stage
steps.

### 4. Hash partitioning

Cache keys are derived from source content + imports + a root hash that
includes `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` content
(see `Cache/Hashing.lean:getRootHash`). Branches with different toolchains
live in disjoint hash spaces, so even within the same container, blobs at
different keys cannot collide unless an attacker can align all root-hash
inputs. With Layer 3 in place, an attacker cannot modify those inputs
between elaboration and pack time.

This layer is insufficient on its own: it depends on Layer 3 to keep the
inputs honest, and on Layer 1 to bound damage if it ever fails.

## CI dispatch: how (repo, branch) gets routed

The composite action at `.github/actions/cache-trust-dispatch/action.yml`
maps each job context to its container, OIDC writer, and read chain. It is
invoked by all three trust-aware jobs:

- **build** — needs `MATHLIB_CACHE_FROM` so pre-build cache gets find what a
  prior run on this same branch uploaded.
- **upload_cache** — needs `MATHLIB_CACHE_PRIMARY` to choose the container
  for `put-staged`.
- **post_steps** — needs `MATHLIB_CACHE_FROM` to verify the roundtrip by
  reading back this CI run's just-uploaded artifacts.

The dispatch is loaded from master / tools-branch — via a sparse checkout
of `workflow-actions/` pinned to `github.workflow_sha` — so PR-supplied
workflow files never override it.

User machines do not apply this dispatch. A maintainer running
`lake exe cache get` locally on a `lean-pr-testing-*` checkout uses the
strict per-repo default and must explicitly opt into widening with
`--cache-from` or `MATHLIB_CACHE_FROM=…`.

## Per-commit namespace for fork-trust uploads

Fork-trust uploads (anything dispatched to `mathlib4-forks`) are namespaced
not only by repo but also by the head commit SHA: paths take the shape
`/f/{repo}/{sha}/{hash}.ltar`. The SHA is sourced from
`github.event.pull_request.head.sha || github.sha` in
`cache-trust-dispatch`, propagated to the cache binary via the
`MATHLIB_CACHE_REPO_SCOPE` environment variable, and applied in
`Cache/Requests.lean:mkFileURL` only when the resulting path is prefixed
(flat paths are unaffected).

This isolates each commit's CI run into its own namespace, which closes
the within-fork temporal replay window: artifacts uploaded by a closed,
hidden, or force-pushed-away PR cannot be read by a later honest PR from
the same fork, because their head SHAs differ. The per-SHA segment
provides the isolation; the `--repo` segment is kept alongside it as an
audit and discoverability handle, letting you list all of a given fork's
uploads in one place.

`master`, `nightly-testing`, and `pr-toolchain-tests` uploads are not
SHA-scoped. Each of these containers receives uploads from a single trust
level, so the container boundary alone suffices for isolation.

## URL paths in each container

`Cache/Infra.lean:Container.flatPath` determines whether artifacts are
stored flat or repo-prefixed; `MATHLIB_CACHE_REPO_SCOPE` (set by
`cache-trust-dispatch` only for `forks` uploads) inserts a SHA segment
between repo and hash on prefixed paths.

- `master` — `/f/{hash}.ltar`
- `forks` — `/f/{repo}/{sha}/{hash}.ltar`
- `nightly-testing`, `pr-toolchain-tests` — `/f/{repo}/{hash}.ltar`

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
- **Validation of artifact byte-identity.** The cache key identifies which
  inputs should have produced an artifact; it does not describe the exact
  bytes inside. A malicious build at hash H produces a poisoned artifact at
  hash H. Containment comes from trust-bounding where that artifact can be
  delivered; fetch-time detection of poisoning is outside the design.

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
