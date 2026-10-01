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
Default reads select the public cache and, where applicable, the consumer’s
own repository and commit namespace. Other scopes require an explicit choice.

## Trust hierarchy and containers

The active model has three destinations:

| Container | Writers | Default read scope |
|-----------|---------|--------------------|
| `master` | mathlib4 `master`/`staging` and `v4.*` release tags | Flat, public artifacts |
| `forks` | mathlib4 PR builds, development branches, and `bors try` | Repository and HEAD SHA |
| `nightly-testing` | All native nightly-testing push builds | Repository and HEAD SHA |

Nightly builds use one R2 bucket, `mathlib4-nightly-testing-cache`. They do not
write to Azure. `pr-toolchain-tests` is retired; its name remains available
only for explicit reads of historical artifacts.

| Consumer | Default lookup chain |
|----------|----------------------|
| mathlib4 | `master` |
| nightly-testing | `master`, `nightly-testing` at HEAD |
| forks (PRs) | `master`, `forks` at HEAD |

The public cache supplies matching upstream artifacts first. A different
nightly toolchain usually causes a public-cache miss. The second destination
serves only the commit that the reader has checked out. Reads never fall back
to an unscoped nightly namespace. A failed HEAD lookup skips the scoped round.

A nightly branch opened as a PR into mathlib4 still uploads to `forks` in
mathlib4 CI. Nightly users can explicitly select that container when needed.
It is not part of the nightly default chain.

## Four enforcement layers

The first two enforce the trust boundary; the last two provide correctness
guarantees and additional containment.

### 1. Token-scoped uploads (server-side)

Before uploading, the workflow obtains a short-lived credential for the writer
identity tied to its container. The identity provider issues the credential
only when the workflow's identity — stamped by GitHub from the repo, event
type, and ref — matches a pre-registered grant. The credential's scope is
fixed when it is issued and cannot be widened afterward.

Azure writes use an OIDC-federated bearer token with one container's RBAC
role. R2 writes use short-lived S3 credentials from the cache broker.

For nightly uploads, the broker matches the nightly repository, its
`cache-upload-nightly-testing` environment, and the `push` event. It derives
the scope from GitHub's signed `sha` claim. The credential permits only:

- `mathlib4-nightly-testing/f/{repo}/{sha}/` for artifacts;
- the exact object `mathlib4-nightly-testing/m/{repo}/{sha}` for the marker.

The caller cannot choose a different repository or SHA. Missing or malformed
SHA claims fail before credentials are minted. The parent token is restricted
to the nightly bucket. Thus, even a compromised uploader cannot write to the
public cache or another commit's nightly namespace.

The fork grant remains container-scoped. Its trusted uploader enforces the
per-commit namespace. Do not assume that the fork credential itself enforces
SHA isolation.

### 2. Isolation of the cache binary

Nightly builds always obtain cache tooling from canonical mathlib4 `master`,
including its `lean-toolchain`. This applies both to the build job's packer
and to the upload job's independently built binary. Nightly branch inputs
cannot select their own tools source. Canonical CI retains its existing
policy: fork PRs use trusted tools, while maintainer branches may test their
own tool changes.

The packer and uploader run on different runner pools. Only the upload job
receives storage credentials. That job handles staged files with trusted
tooling on a fresh runner; it does not execute the branch under test.

Stopping experimental Lean branch pushes is not the security boundary. If
such a branch runs again, its artifacts still remain under its own SHA, and
its compiler does not build the uploader.

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

## Per-commit namespaces

Both `forks` and `nightly-testing` use `f/{repo}/{sha}/{hash}.ltar`.
A closed, hidden, or force-pushed-away branch cannot supply artifacts to a
later commit through the default read chain. CI sets
`MATHLIB_CACHE_REPO_SCOPE` to the build SHA; local reads default to HEAD.

`cache get --scope=SHA` selects another commit explicitly. `cache get --unsafe`
discovers recent cached commits, with `--unsafe-window=N` controlling their
number. Both choices print the non-default-scope security notice. Marker
queries use `nightly-testing` for that repository and `forks` for other
noncanonical repositories.

SHA scoping bounds replay; it does not validate artifact bytes. A reader
already trusts code from its checked-out commit. Reading another commit's
artifacts adds that commit's producer to the trust decision.

## Nightly cutover

Deploy the broker's commit-scoped grant before enabling nightly R2 uploads.
Configure the nightly environment and broker URL, then land the client and
workflow changes on canonical master before nightly workflows consume them.
The nightly R2 destination variable is
`MATHLIB_CACHE_R2_NIGHTLY_PUT_BASE_URL`, the account S3 endpoint plus bucket.

Start with fresh SHA-scoped uploads. Do not relabel either old nightly
container's artifacts as trusted commit uploads. Retire the Azure fallback
for `mathlib4-nightly-testing` when the new path is enabled. Historical cache
objects can remain in storage for old clients or explicit recovery.

## Explicitly out of scope

The trust model does not attempt to defend against:

- **Compromised upstream Lean releases** — a malicious toolchain on the trusted
  branch builds the cache binary itself.
- **Compromised storage tenant** — admin-level compromise defeats the access
  grants.
- **Substituted read endpoint** — the cache does not verify downloaded bytes, so
  whichever host answers a read carries the storage tenant's trust. That is the
  default read host `https://cache.mathlib.org`, or a host named by
  `MATHLIB_CACHE_GET_URL`.
- **Substituted write endpoint** — the cache does not verify the host it uploads
  to: whichever host `MATHLIB_CACHE_PUT_URL` or `MATHLIB_CACHE_PUT_BASE_URL`
  names receives the upload, and on the azure backend the bearer token with it.
  The trusted branch's workflow defines the upload job's environment, and a
  token captured this way stays bounded by Layer 1.
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
| Read-fallback resolution, dispatch             | [`Cache/Requests.lean`](Requests.lean) (`effectiveGetURLs`)      |
| Backend selection, destination arbitration     | [`Cache/Upload/Defs.lean`](Upload/Defs.lean) (`UploadBackend`, `stagedUploadDest`), [`Cache/Upload.lean`](Upload.lean) (`runPut`) |
| Upload backends: credentials, destination, signing, transfer | [`Cache/Upload/Azure.lean`](Upload/Azure.lean), [`Cache/Upload/S3.lean`](Upload/S3.lean) |
| Transfer tool mechanics                        | [`Cache/Upload/Curl.lean`](Upload/Curl.lean), [`Cache/Upload/Rclone.lean`](Upload/Rclone.lean), [`Cache/Upload/Dest.lean`](Upload/Dest.lean) |
| Trust property tests                           | [`Cache/Test.lean`](Test.lean)                                   |
| User-facing CLI surface, env vars              | [`Cache/Main.lean`](Main.lean), [`Cache/README.md`](README.md), [`Cache/CI.md`](CI.md) |
| OIDC mint + per-job dispatch                   | [`.github/workflows/build_template.yml`](../.github/workflows/build_template.yml) (`upload_cache` job) |
| (repo, ref) → trust class policy table         | [`.github/actions/cache-trust-dispatch/action.yml`](../.github/actions/cache-trust-dispatch/action.yml) |
| Caller `cache_application_id` wiring           | [`.github/workflows/build.yml`](../.github/workflows/build.yml), [`bors.yml`](../.github/workflows/bors.yml), [`build_fork.yml`](../.github/workflows/build_fork.yml), [`ci_dev.yml`](../.github/workflows/ci_dev.yml), [`release_cache.yml`](../.github/workflows/release_cache.yml) |
