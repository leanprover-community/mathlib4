# Mathlib Cache

This directory contains the implementation of Mathlib's build cache system (`lake exe cache`), which downloads pre-built `.olean` files to avoid recompiling the entire library.

> **Note**: A new `lake cache` command is currently being designed and implemented in Lake itself. This will eventually replace the Mathlib-specific `lake exe cache` and work for all repositories. Until then, this cache system remains the primary way to get pre-built artifacts for Mathlib.

## Quick Start

```bash
# Download and unpack cache for all of Mathlib
lake exe cache get

# Force re-download everything
lake exe cache get!

# Download cache for specific files only (and their dependencies)
lake exe cache get Mathlib/Algebra/Group/Basic.lean
lake exe cache get Mathlib.Algebra.Group.Basic
```

## Commands

### No Privilege Required

| Command         | Description                                                         |
|-----------------|---------------------------------------------------------------------|
| `get [ARGS]`    | Download linked files missing on the local cache and decompress     |
| `get! [ARGS]`   | Download all linked files and decompress (force re-download)        |
| `get- [ARGS]`   | Download linked files missing to local cache, but do not decompress |
| `pack`          | Compress non-compressed build files into the local cache            |
| `pack!`         | Compress build files into the local cache (no skipping)             |
| `unpack`        | Decompress linked already downloaded files                          |
| `unpack!`       | Decompress linked already downloaded files (no skipping)            |
| `clean`         | Delete non-linked files                                             |
| `clean!`        | Delete everything on the local cache                                |
| `lookup [ARGS]` | Show information about cache files for the given Lean files         |

### Privilege Required (CI/Maintainers)

| Command        | Description                                               |
|----------------|-----------------------------------------------------------|
| `put`          | Run `pack` then upload linked files missing on the server |
| `put!`         | Run `pack` then upload all linked files                   |
| `put-unpacked` | `put` only files not already packed; intended for CI use  |
| `commit`       | Write a commit on the server                              |
| `commit!`      | Overwrite a commit on the server                          |

### Arguments

The `get`, `get!`, `get-`, and `lookup` commands accept:

- Module names: `Mathlib.Algebra.Group.Basic`
- File paths: `Mathlib/Algebra/Group/Basic.lean`
- Folder names: `Mathlib/Data/` (finds all Lean files inside)
- Glob patterns: `Mathlib/**/Order/*.lean` (via shell expansion)

When arguments are provided, only the specified files and their transitive imports are downloaded.

### Options

| Option              | Description                                                                                |
|---------------------|--------------------------------------------------------------------------------------------|
| `--repo=OWNER/REPO` | Override the repository to fetch cache from (e.g., `--repo=leanprover-community/mathlib4`) |
| `--cache-from=LIST` | For `get`/`get!`/`get-`/`lookup`: trust-ordered, comma-separated list of containers to read from. Overrides the per-repo default (see [Trust-ordered containers](#trust-ordered-containers)). |
| `--container=NAME`  | For `put`/`put!`/`put-unpacked`/`put-staged`/`commit`/`commit!`: target container for upload. Required unless `MATHLIB_CACHE_PUT_URL` is set. |

Container names (known to both flags): `master`, `forks`, `nightly-testing`, `pr-toolchain-tests`, `legacy`.

## Trust-ordered containers

The cache is split across multiple Azure Blob Storage containers on the
`lakecache` storage account, each fed by a CI job at a known trust level:

| Container                          | Written by                          | Trust  |
|------------------------------------|-------------------------------------|--------|
| `mathlib4-master`                  | master CI                           | high   |
| `mathlib4-forks`                   | PR builds (forks)                   | medium |
| `mathlib4-nightly-testing`         | `nightly-testing` branch builds     | medium |
| `mathlib4-pr-toolchain-tests`      | toolchain-PR test runs              | medium |
| `mathlib4` (legacy)                | master CI only, during the migration | high (writes restricted) |

`cache get` tries each repo's dedicated container first and falls back to the
**legacy** `mathlib4` container as a universal last-resort. A poisoned artifact
in a low-trust source will only be served when the higher-trust source does
not have it — the worst case is a missed cache hit (rebuild from source)
rather than a corrupted build.

> **Where the trust is actually enforced.** The CLI dispatch in CI is best-effort;
> the real boundary is at the Azure auth layer. Each CI job mints an OIDC-issued
> bearer token whose scope authorizes writes only to the container(s) appropriate
> for that job's context. A fork PR's token cannot write `mathlib4-master` even
> if the cache invocation were tampered with — Azure would reject the PUT.

The `mathlib4` container is the historical monolithic bucket where every CI
job used to write. During the migration, **only master CI dual-writes to
`legacy`** (alongside its own `mathlib4-master` upload) so that consumers
running older cache tools — which only know how to read from `mathlib4` —
keep finding master-built artifacts at the historical location. Fork and
nightly-testing CI **do not** write to `legacy`: allowing low-trust writers
into it would re-introduce the cross-trust poisoning vector this migration
is designed to eliminate. Once all readers have moved to the new containers,
the master dual-write to `legacy` can be turned off.

The default trust-ordered list applied to each repo is:

| GitHub repo                                     | Container order tried             |
|-------------------------------------------------|-----------------------------------|
| `leanprover-community/mathlib4` (master)        | `master`, `legacy`                |
| `leanprover-community/mathlib4-nightly-testing` | `nightly-testing`, `legacy` *(strict)* |
| any fork (PRs)                                  | `forks`, `legacy`                 |

Note that `master` is *not* in the fork/nightly fallback lists: that container
stores only canonical mathlib4 paths (`/f/{hash}.ltar`), never fork-prefixed
ones, so a lookup there from a fork iteration would always 404. Fork PRs still
read master-built artifacts — via the outer repo loop iteration where
`repo = MATHLIBREPO` uses the canonical path scheme against `master`.

**Branch-aware widening for the nightly-testing repo.** The default above is
the *strict* trusted-nightly view: `pr-toolchain-tests` is deliberately
excluded so trusted consumers (`nightly-testing`, `nightly-testing-green`,
`bump/*`) never silently fall back to artifacts uploaded by low-trust
toolchain-PR test branches. When the cache tool detects it's running on a
toolchain-test branch (`lean-pr-testing-*`, `batteries-pr-testing-*`, etc.)
via `getRemoteRepo`, it widens the allowlist for that run to
`[pr-toolchain-tests, nightly-testing, legacy]` so the branch can read its
own previously-uploaded artifacts. The classification lives in
`containersForRepoAndBranch` (in `Cache/Infra.lean`).

Use `--cache-from=master` to read **only** from the new master container
(strictest mode). Use `--cache-from=master,legacy` (the migration default for
the master branch) or any other explicit ordering for ad-hoc situations.

Uploads should explicitly target a single container via `--container=NAME`.
If neither `--container` nor `MATHLIB_CACHE_PUT_URL` is set, the upload
defaults to **`legacy`** with a deprecation warning to stderr — a transitional
fallback so workflow files written before the per-trust-level split keep
working while every branch is being rebased onto the new YAMLs. The default
will be tightened to a hard error once all known consumers have migrated.

To keep unmigrated readers' hit rates during the transition, **only master CI**
runs `put` twice: once with `--container=master` and once with
`--container=legacy`. Fork and nightly-testing CI write only to their own
dedicated containers (`forks`, `nightly-testing`) and never to `legacy`.

> **Note**: `MATHLIB_CACHE_GET_URL` and `MATHLIB_CACHE_PUT_URL` (see below)
> still work as a back-compat single-URL override; when either is set, the
> multi-container logic is bypassed for that direction.

## Environment Variables

### Cache Location

| Variable            | Description                        | Default                                         |
|---------------------|------------------------------------|-------------------------------------------------|
| `MATHLIB_CACHE_DIR` | Directory for cached `.ltar` files | `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` |

### Custom Cache URLs

These allow overriding the cache endpoints, useful for mirrors or custom deployments:

| Variable                | Description                     | Default                                              |
|-------------------------|---------------------------------|------------------------------------------------------|
| `MATHLIB_CACHE_GET_URL` | URL for downloading cache files | Azure container URLs (see [containers](#trust-ordered-containers)) |
| `MATHLIB_CACHE_PUT_URL` | URL for uploading cache files   | Azure container URL chosen by `--container=NAME`     |

### Authentication (for uploads)

| Variable                 | Description                            |
|--------------------------|----------------------------------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure bearer token (preferred)  |
| `MATHLIB_CACHE_SAS`      | Azure SAS token fallback               |

## How It Works

### File Hashing

Each Lean file's cache is identified by a hash computed from:

1. **Root hash**: A combination of:
   - `lakefile.lean` content
   - `lean-toolchain` content
   - `lake-manifest.json` content
   - The Lean compiler's git hash
   - A generation counter (bumped to invalidate all caches)

2. **File hash**: Mixing:
   - The root hash
   - The file's path relative to its package
   - The file's content hash
   - Hashes of all imported files

This ensures that any change to toolchain, dependencies, or source files produces a different cache key.

### Cache File Format

Cache files use the `.ltar` format (Lean tar), handled by [leantar](https://github.com/digama0/leangz). Each `.ltar` contains:

- `.olean` files (compiled Lean)
- `.ilean` files (interface info)
- `.trace` files (build traces)
- `.c` files (generated C code)
- Associated `.hash` files

### Cached Packages

The cache covers these packages:

- `Mathlib`
- `Batteries`
- `Aesop`
- `Cli`
- `ImportGraph`
- `LeanSearchClient`
- `Plausible`
- `Qq`
- `ProofWidgets`
- `Archive`
- `Counterexamples`

## Default Cache Backend

### Azure Blob Storage

All cache containers live on the `lakecache` Azure storage account; see
[Trust-ordered containers](#trust-ordered-containers) for the per-container URLs.

## Setting Up Your Own Cache Endpoint

You can host your own cache mirror or private cache on any HTTP server with
Azure-compatible PUT semantics.

### Requirements

Your endpoint must support:

1. **GET requests** for downloading files at:
   - `/f/{hash}.ltar` — for the canonical mathlib4 cache
   - `/f/{repo}/{hash}.ltar` — for fork caches
   - `/c/{commit_hash}` — for commit manifests

2. **PUT requests** for uploading (if you need upload capability)

### Using a Custom Endpoint

```bash
# Download from a custom mirror (bypasses multi-container logic)
export MATHLIB_CACHE_GET_URL="https://my-mirror.example.com/mathlib4"
lake exe cache get

# Upload to a custom endpoint
export MATHLIB_CACHE_PUT_URL="https://my-upload.example.com/mathlib4"
export MATHLIB_CACHE_AZURE_BEARER_TOKEN="your-bearer-token"  # preferred
# export MATHLIB_CACHE_SAS="your-sas-token"                  # fallback
lake exe cache put
```

### Example: Simple HTTP Mirror

For a read-only mirror using nginx or any static file server:

1. Periodically sync files from the official cache
2. Serve them at a public URL
3. Point users to your mirror:

```bash
export MATHLIB_CACHE_GET_URL="https://mathlib-mirror.myorg.com"
lake exe cache get
```

### URL Structure

The cache uses this URL pattern:

```
{BASE_URL}/f/{repo}/{filename}.ltar  # Fork/branch caches
{BASE_URL}/f/{filename}.ltar         # Main mathlib cache (Azure)
{BASE_URL}/c/{commit_hash}           # Commit manifests
```

Where:
- `{repo}` is like `leanprover-community/mathlib4` or `username/mathlib4`
- `{filename}` is a hash like `1234567890abcdef`
- `{commit_hash}` is a git commit SHA

## Tests

The cache tool's pure logic (container URL construction, per-repo allowlist,
CLI parsing) is covered by a standalone test exe:

```bash
lake exe cache-test
```

The exe builds only `Cache.*` and its direct deps — it does not require
Mathlib or `MathlibTest`. Exits 0 on success, non-zero on failure.

> A Lake package has a single `testDriver`, which the enclosing `mathlib`
> package already binds to `MathlibTest`. If the cache tool ever moves to
> its own Lake project, the `cache-test` exe can be promoted to that
> project's `testDriver` so `lake test` invokes it directly.

## Dependencies

The cache system automatically downloads and manages:

- **curl** (>=7.70, preferably >=7.81) - for HTTP transfers
- **leantar** - for `.ltar` compression/decompression

If your system curl is too old, a static binary is downloaded automatically on Linux.

## File Locations

| Path                        | Description                  |
|-----------------------------|------------------------------|
| `~/.cache/mathlib/`         | Default cache directory      |
| `~/.cache/mathlib/*.ltar`   | Cached build artifacts       |
| `~/.cache/mathlib/curl.cfg` | Temporary curl configuration |
| `.lake/build/lib/lean/`     | Unpacked `.olean` files      |
| `.lake/build/ir/`           | Unpacked `.c` files          |
