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

## Environment Variables

### Cache Location

| Variable            | Description                        | Default                                         |
|---------------------|------------------------------------|-------------------------------------------------|
| `MATHLIB_CACHE_DIR` | Directory for cached `.ltar` files | `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib` |

### Cache Backend Selection

| Variable                       | Description                                              | Default     |
|--------------------------------|----------------------------------------------------------|-------------|
| `MATHLIB_CACHE_USE_CLOUDFLARE` | Set to `1` or `true` to use Cloudflare R2 instead of Azure | Azure cache |

### Custom Cache URLs

These allow overriding the cache endpoints, useful for mirrors or custom deployments:

| Variable                | Description                     | Default                                                           |
|-------------------------|---------------------------------|-------------------------------------------------------------------|
| `MATHLIB_CACHE_GET_URL` | URL for downloading cache files | Azure or Cloudflare URL based on `MATHLIB_CACHE_USE_CLOUDFLARE`   |
| `MATHLIB_CACHE_PUT_URL` | URL for uploading cache files   | Azure or Cloudflare URL based on `MATHLIB_CACHE_USE_CLOUDFLARE`   |

### Authentication (for uploads)

| Variable                 | Description                                    |
|--------------------------|------------------------------------------------|
| `MATHLIB_CACHE_SAS`      | Azure SAS token (when using Azure backend)     |
| `MATHLIB_CACHE_S3_TOKEN` | S3 credentials (when using Cloudflare backend) |

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

## Default Cache Backends

### Azure Blob Storage (Default)

- **Download URL**: `https://lakecache.blob.core.windows.net/mathlib4`
- Used by default for downloads and uploads

### Cloudflare R2

- **Download URL**: `https://mathlib4.lean-cache.cloud`
- **Upload URL**: `https://a09a7664adc082e00f294ac190827820.r2.cloudflarestorage.com/mathlib4`
- Enable with `MATHLIB_CACHE_USE_CLOUDFLARE=1`

## Setting Up Your Own Cache Endpoint

You can host your own cache mirror or private cache using any S3-compatible storage or HTTP server.

### Requirements

Your endpoint must support:

1. **GET requests** for downloading files at:
   - `/f/{repo}/{hash}.ltar` - for fork caches
   - `/f/{hash}.ltar` - for main mathlib cache (Azure only)
   - `/c/{commit_hash}` - for commit manifests

2. **PUT requests** for uploading (if you need upload capability)

### Using a Custom Endpoint

```bash
# Download from a custom mirror
export MATHLIB_CACHE_GET_URL="https://my-mirror.example.com/mathlib4"
lake exe cache get

# Upload to a custom endpoint
export MATHLIB_CACHE_PUT_URL="https://my-upload.example.com/mathlib4"
export MATHLIB_CACHE_SAS="your-auth-token"  # or MATHLIB_CACHE_S3_TOKEN for S3
lake exe cache put
```

### Example: S3-Compatible Storage

For S3-compatible storage (MinIO, Cloudflare R2, AWS S3, etc.):

1. Create a bucket (e.g., `mathlib-cache`)
2. Configure public read access for downloads (or use signed URLs)
3. Set up authentication for uploads
4. Set the environment variables:

```bash
export MATHLIB_CACHE_GET_URL="https://your-bucket.s3.region.amazonaws.com/mathlib-cache"
export MATHLIB_CACHE_PUT_URL="https://your-bucket.s3.region.amazonaws.com/mathlib-cache"
export MATHLIB_CACHE_USE_CLOUDFLARE=1  # Use S3-style auth
export MATHLIB_CACHE_S3_TOKEN="ACCESS_KEY:SECRET_KEY"
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
