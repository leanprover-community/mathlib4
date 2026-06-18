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
| `query`         | Find the most recent commit with cached entries on the current branch |

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
| `--scope=REF`       | For `get`/`get!`/`get-`: read from the SHA-scoped namespace for the given git ref (anything `git rev-parse` accepts: `HEAD`, branch, tag, SHA). Use the SHA reported by `cache query`. Triggers the non-default-scope security notice. |
| `--unsafe`          | For `get`/`get!`/`get-`: instead of pinning one `--scope`, automatically walk this branch's history and read the `forks` container at the most recent cached fork commit (newest first if `--unsafe-window` allows more than one), until the cache is satisfied (see [Unsafe automatic scope walk](#unsafe-automatic-scope-walk)). Mutually exclusive with `--scope`; always triggers the security notice. |
| `--unsafe-window=N` | Number of cached fork commits `--unsafe` will try (default `1`). Implies `--unsafe`. |
| `--container=NAME`  | For `put`/`put!`/`put-unpacked`/`put-staged`/`commit`/`commit!`: target container for upload. |

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
| any fork (PRs)                                  | `master`, `forks`, `legacy` |

Override the read chain with `--cache-from=LIST`:

```bash
# Read only from the master container
lake exe cache get --cache-from=master

# Read master first, then forks
lake exe cache get --cache-from=master,forks
```

Uploads target a single container via `--container=NAME`.

## Environment Variables

| Variable            | Description                        | Default                                         |
|---------------------|------------------------------------|-------------------------------------------------|
| `MATHLIB_CACHE_DIR` | Directory for cached `.ltar` files | `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` |

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

## Finding Cached Commits with `query`

For branches with per-commit SHA scoping (e.g., fork PRs), you can use
`lake exe cache query` to discover which recent commits on your branch have
cached entries. This is useful when your current branch has diverged from
upstream and you want to avoid waiting for CI to build everything.

```bash
# Find the most recent cached commit on the current branch
lake exe cache query

# Example output:
# Most recent cached commit on branch: 5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e
# Repository: leanprover-community/mathlib4
# Container: forks
#
# To use this cache, run:
#   lake exe cache get --scope=5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e
```

The `query` command walks your git log backwards from `HEAD`, stopping at the
merge base with `master` or a hard cap of 50 commits (whichever comes first),
and probes each commit for a completed SHA-scoped upload in the `forks`
container. That signal is written by `put-staged` only after a successful
upload, so its presence is a reliable "this commit was cached" signal. `query`
prints the SHA to stdout (and does not auto-apply it) — you manually copy the
result into your `cache get` command if desired.

### Boolean probe on a single commit

`lake exe cache query <REF>` checks a specific commit and exits with 0 (cached)
or 1 (not cached). The ref can be `HEAD`, a branch name, a tag, or a SHA — anything
`git rev-parse` accepts.

```bash
# Is the current checkout's HEAD cached?
lake exe cache query HEAD && echo "yes" || echo "no"

# Is a specific SHA cached?
lake exe cache query 5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e
# prints "cached: 5a3c7e9a..." (exit 0) or "not cached: 5a3c7e9a..." (exit 1)
```

By default `query` (both modes) targets the cwd's git remote — pass `--repo=`
to override.

### Unsafe automatic scope walk

`cache get --unsafe` folds the `query` discovery into the download itself: rather
than asking you to copy one SHA into `--scope=`, it walks your branch history
(`HEAD` back to the merge base with `master`) for commits that have a cached fork
build and reads the `forks` container at their scope. By
default it uses just the single most recent such commit; `--unsafe-window=N`
widens this to the `N` most recent, tried newest first with files fetched in one
round dropped from the next.

```bash
lake exe cache get --unsafe             # use the most recent cached fork commit
lake exe cache get --unsafe-window=10   # try the 10 most recent (implies --unsafe)
```

The trust-ordered container chain is unchanged: `master` is still tried first and
serves the bulk of every fork's files by hash; only the `forks` round is expanded
into one round per discovered SHA. If no cached fork commit is found in range,
`--unsafe` falls back to a plain unscoped read.

`--unsafe` trusts the artifacts of *every* commit it tries, so it always prints
the [non-default-scope security notice](#security-warning-non-default-scope). It
is mutually exclusive with `--scope=` (which pins exactly one commit).

### Heads-up note from `cache get`

When you run `cache get` on a fork-trust repo and HEAD has not been built and
cached at fork-trust level, the tool prints a stderr note pointing you at
`cache query` (and warning that picking a different commit means trusting its
artifacts). Costs one HTTP HEAD per `cache get` invocation; only fires when the
resolved repo's default chain includes `forks` and no `--scope=` / `--cache-from`
override is supplied.

## Security Warning: Non-Default Scope

When you read cache artifacts at a non-default scope, the cache tool prints a
security warning to stderr. This happens when:

1. **`--unsafe` is passed** — you are letting the tool walk history and trust the
   artifacts of whichever recent fork commit(s) it finds cached.
2. **`--scope=` is passed** — you are reading from a specific commit's
   namespace instead of the repo's default trust chain.
3. **`--cache-from` widens the read chain** — you are explicitly telling the tool
   to trust containers beyond the repo default.
4. **`--repo` overrides the detected git remote** — you are reading cache for a
   different repository than your cwd's git remote.

Example warning:

```
=================================================================
SECURITY: reading cache at a non-default scope
=================================================================
You are reading cache artifacts at a scope outside the default trust
boundary for this repo. The cache cannot verify the contents of these
artifacts; you are choosing to trust whoever uploaded them.

Repository: leanprover-community/mathlib4
Reason: --scope=5a3c7e9a2f8c1d6b4e0f9a2c3d4e5f6a7b8c9d0e (explicit per-commit scope)
=================================================================
```

This warning is always printed — it cannot be suppressed with `--quiet`. The
warning is purely informational; it does not prompt for confirmation (so it
doesn't interfere with CI).

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
