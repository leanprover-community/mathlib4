# Mathlib Cache

This directory contains the implementation of Mathlib's build cache system (`lake exe cache`), which downloads pre-built `.olean` files to avoid recompiling the entire library.

> **Note**: A new `lake cache` command is currently being designed and implemented in Lake itself. This will eventually replace the Mathlib-specific `lake exe cache` and work for all repositories. Until then, this cache system remains the primary way to get pre-built artifacts for Mathlib.

> **Trust model & security**: see [`SECURITY.md`](./SECURITY.md) for the
> trust model behind the multi-container split, and [`WORKFLOWS.md`](./WORKFLOWS.md)
> for the three workflows the tool runs.

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

### Reading and local maintenance

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
| `query`         | Find the most recent commit of the branch that CI has cached (developer-cache workflow) |


### Operating an external cache

The upload commands (`put`, `put!`, `put-staged`) are internal to mathlib CI and documented in [`CI.md`](./CI.md); public consumers of this tool should not rely on their details.

A custom cache can rely on the staging commands:

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `stage`     | Copy files not already `pack`ed to `--staging-dir`                   |
| `stage!`    | Copy all linked cache files to `--staging-dir`                       |
| `unstage`   | Copy `*.ltar` files from `--staging-dir` into the local cache        |
| `unstage!`  | Same, overwriting files that already exist in the local cache        |

To operate an external cache, run `stage` to produce the artifact set, upload
it under an `f/` prefix with any storage client, and point readers at the
endpoint with `MATHLIB_CACHE_GET_URL`. A reader with that variable set takes
the [public-cache workflow](./WORKFLOWS.md#the-public-cache-workflow) whatever
repository its checkout names, and `get` requests `{endpoint}/f/{hash}.ltar`;
`stage` writes the `.ltar` files flat into the staging directory, so the
upload adds the `f/` segment.

Example:

```bash
# Produce the artifact set for your endpoint:
lake exe cache stage --staging-dir=./cache-out
# Upload it under the endpoint's f/ prefix, with any storage client:
rclone copy ./cache-out remote:my-bucket/my-prefix/f/
# Point readers at the endpoint:
MATHLIB_CACHE_GET_URL=https://cache.example.org/my-prefix lake exe cache get
```

### Arguments

The `get`, `get!`, `get-`, and `lookup` commands accept:

- Module names: `Mathlib.Algebra.Group.Basic`
- File paths: `Mathlib/Algebra/Group/Basic.lean`
- Folder names: `Mathlib/Data/` (finds all Lean files inside)
- Glob patterns: `Mathlib/**/Order/*.lean` (via shell expansion)

When arguments are provided, only the specified files and their transitive imports are downloaded.

### Flags

Each command declares its flags; `lake exe cache <command> --help` lists them.
A flag follows the command (`lake exe cache get --repo=OWNER/REPO`); a flag
before the command is moved after it. A command rejects a flag it does not
declare, and a workflow rejects the flags of another workflow.

| Flag                | Description                                                                                |
|---------------------|--------------------------------------------------------------------------------------------|
| `--repo=OWNER/REPO` | For `get`/`get!`/`get-`/`query`: the repository whose cache to read (e.g., `--repo=leanprover-community/mathlib4`). Selects the workflow. |
| `--cache-from=LIST` | For `get`/`get!`/`get-` under the developer-cache and nightly workflows: the trust-ordered, comma-separated list of containers to read, replacing the workflow's chain (see [Trust-ordered containers](./WORKFLOWS.md#trust-ordered-containers)). |
| `--scope=REF`       | For `get`/`get!`/`get-` under the developer-cache and nightly workflows: the commit whose fork cache to read, as any git ref (see [`query`](./WORKFLOWS.md#finding-cached-commits-with-query)). |
| `--unsafe`          | For `get`/`get!`/`get-` under the developer-cache workflow: read the most recent cached fork commits of the branch, found automatically (see [Unsafe automatic scope walk](./WORKFLOWS.md#unsafe-automatic-scope-walk)). |
| `--unsafe-window=N` | The number of cached fork commits `--unsafe` tries (default `1`). Implies `--unsafe`. |
| `--staging-dir=DIR` | For `stage`/`stage!`/`unstage`/`unstage!`: the staging directory. Required. |

The public-cache workflow has no flags of its own; the others are listed per
workflow in [`WORKFLOWS.md`](./WORKFLOWS.md#which-workflow-runs).

## Workflows

`lake exe cache get` runs one of three workflows, chosen from the repository
your checkout names (its git remote, or `--repo=OWNER/REPO`) and the flags,
and prints the one it runs. [`WORKFLOWS.md`](./WORKFLOWS.md) describes the
three in full.

**If you have Mathlib as a dependency**, or work on a checkout of
`leanprover-community/mathlib4` itself, `lake exe cache get` runs the
public-cache workflow. It fetches each file once from the public cache at
`https://cache.mathlib.org/mathlib4` and nothing else. No flag is needed.

**If you are a mathlib developer working on a fork**, `lake exe cache get`
runs the developer-cache workflow. It reads mathlib's `master` cache first,
then your fork's own cache for the commit you have checked out, which CI
fills when it builds your PR. `lake exe cache query` lists the commits of your
branch that CI has cached, and `--scope=SHA` reads one of them. Reading
another commit's artifacts means trusting whoever built them, so the tool
prints a security notice when you do.

The nightly workflow serves the nightly-testing repository.

## Environment Variables

| Variable                         | Description                        | Default                                         |
|----------------------------------|------------------------------------|-------------------------------------------------|
| `MATHLIB_CACHE_DIR`              | Directory for cached `.ltar` files | `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` |
| `MATHLIB_CACHE_GET_URL`          | Download from this single URL as a flat namespace (see [Operating an external cache](#operating-an-external-cache)) | unset |
| `MATHLIB_CACHE_DEBUG_USE_LEGACY` | See [Troubleshooting](#troubleshooting) | unset |

An empty value means unset. The variables of the chain read
(`MATHLIB_CACHE_FROM`, `MATHLIB_CACHE_REPO_SCOPE`) are listed in
[`WORKFLOWS.md`](./WORKFLOWS.md#environment-variables); the upload variables
are internal to mathlib CI, see [`CI.md`](./CI.md).

## Troubleshooting

The cache endpoints have been available since September 2026. The cache client provides an environment variable `MATHLIB_CACHE_DEBUG_USE_LEGACY` to read both caches from the Azure storage account instead, the behavior before the endpoints were available, for troubleshooting any issues that might arise in the transition:

```bash
# bash, zsh, Git Bash
MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get

# PowerShell
$env:MATHLIB_CACHE_DEBUG_USE_LEGACY = 1; lake exe cache get

# Windows CMD
set MATHLIB_CACHE_DEBUG_USE_LEGACY=1
lake exe cache get
```

The variable is intended as a troubleshooting fallback and it might be retired at any time.


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

The cache tool's pure logic (container URL construction, the workflow
decision, the command line) is covered by a standalone test exe:

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

- **curl** (>=7.75, preferably >=7.81) - for HTTP transfers
- **leantar** - for `.ltar` compression/decompression

If your system curl is too old, a static binary is downloaded automatically on Linux.

## File Locations

| Path                        | Description                  |
|-----------------------------|------------------------------|
| `~/.cache/mathlib/`         | Default cache directory      |
| `~/.cache/mathlib/*.ltar`   | Cached build artifacts       |
| `~/.cache/mathlib/*.ltar.<pid>.part` | Downloads in flight, renamed on success |
| `~/.cache/mathlib/curl-<pid>.cfg` | Temporary curl configuration |
| `.lake/build/lib/lean/`     | Unpacked `.olean` files      |
| `.lake/build/ir/`           | Unpacked `.c` files          |

The cache directory is per user, not per checkout, so several `cache` runs can
be in flight in it at once. Everything temporary is therefore named with the
writing process's id, and one run only ever renames or removes its own files.
