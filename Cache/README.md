# Mathlib Cache

This directory contains the implementation of Mathlib's build cache system (`lake exe cache`), which downloads pre-built `.olean` files to avoid recompiling the entire library.

> **Note**: A new `lake cache` command is currently being designed and implemented in Lake itself. This will eventually replace the Mathlib-specific `lake exe cache` and work for all repositories. Until then, this cache system remains the primary way to get pre-built artifacts for Mathlib.

> **Trust model & security**: see [`SECURITY.md`](./SECURITY.md) for the
> trust model behind the multi-container split.

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
`lakecache` storage account. Container names accepted by `--container=NAME`
and `--cache-from=LIST`: `master`, `forks`, `nightly-testing`,
`pr-toolchain-tests`, `legacy`.

`cache get` resolves a file by trying a default chain of containers in
order, depending on the repo:

| GitHub repo                                     | Container order tried       |
|-------------------------------------------------|-----------------------------|
| `leanprover-community/mathlib4`                 | `master`, `legacy`          |
| `leanprover-community/mathlib4-nightly-testing` | `nightly-testing`, `legacy` |
| any fork (PRs)                                  | `forks`, `legacy`           |

Override the read chain with `--cache-from=LIST` (CLI) or
`MATHLIB_CACHE_FROM` (env var):

```bash
# Read only from the master container
lake exe cache get --cache-from=master

# Read master first, then forks
lake exe cache get --cache-from=master,forks
```

Uploads target a single container via `--container=NAME`.

## Environment Variables

### Cache Location

| Variable            | Description                        | Default                                         |
|---------------------|------------------------------------|-------------------------------------------------|
| `MATHLIB_CACHE_DIR` | Directory for cached `.ltar` files | `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` |

### Custom Cache URLs

Override the cache endpoints. When either is set, the multi-container
resolution is bypassed for that direction.

| Variable                | Description                     | Default                                              |
|-------------------------|---------------------------------|------------------------------------------------------|
| `MATHLIB_CACHE_GET_URL` | URL for downloading cache files | Azure container URLs (see [containers](#trust-ordered-containers)) |
| `MATHLIB_CACHE_PUT_URL` | URL for uploading cache files   | Azure container URL chosen by `--container=NAME`     |

### Read fallback chain

| Variable             | Description                                                          | Default                |
|----------------------|----------------------------------------------------------------------|------------------------|
| `MATHLIB_CACHE_FROM` | Comma-separated container list (same shape as `--cache-from`). `--cache-from` (CLI) takes precedence when both are set. | per-repo default chain |

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
