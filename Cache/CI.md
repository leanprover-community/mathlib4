# Mathlib cache: CI uploads

The upload logic in `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it. External consumers should not depend
on them.

The trust model behind the containers and the write credentials is in [`SECURITY.md`](./SECURITY.md).

## Upload commands

An upload writes one container, which `--container` names, under the
container's root: the container on the Azure storage account, or the URL
`MATHLIB_CACHE_PUT_URL` names. The container decides the layout under the
root. `master` is flat, `{root}/f/{hash}.ltar`. The other containers are
repo-namespaced, `{root}/f/{repo}/{hash}.ltar`. With a per-commit scope,
`forks` writes the fork's namespace `{root}/f/{repo}/{sha}/{hash}.ltar`
followed by the completeness marker `{root}/m/{repo}/{sha}` that `cache query`
probes.

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `put`       | Run `pack`, then upload the files this build links from the local cache. The build graph scopes the upload: nothing else in the shared per-user cache directory is uploaded. |
| `put!`      | Same as `put`, overwriting files the server already holds             |
| `put-staged`| Upload the `*.ltar` files in `--staging-dir`. CI uploads with this command; `--backend` selects the storage backend. |

## Upload options

| Option              | Description                                          |
|---------------------|------------------------------------------------------|
| `--container=NAME`  | The target container: `master`, `forks`, `nightly-testing`, or `pr-toolchain-tests`. Required. The container decides the layout under its root: flat (`f/{hash}.ltar`) for `master`, repo-namespaced (`f/{repo}/{hash}.ltar`) for the others, and with a scope the per-commit namespace (`f/{repo}/{sha}/{hash}.ltar`) of `forks`. `legacy` is read-only. |
| `--repo=OWNER/REPO` | For a repo-namespaced container: the repository the upload is for. The default is the canonical repository, whose own PR branches build with fork trust; uploads probe no git remote. `master` ignores it. |
| `--scope=REF`       | The per-commit namespace to upload under, and its completeness marker. Only `forks` has per-commit namespaces; a scope on another container is an error. Takes precedence over `MATHLIB_CACHE_REPO_SCOPE`. The read-side use of `--scope` is documented in [`WORKFLOWS.md`](./WORKFLOWS.md). |
| `--backend=NAME`    | The storage backend, `azure` (the default) or `s3` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload. Required. |

`lake exe cache <command> --help` lists the flags of each command.

## How CI uploads

The trust dispatch (`.github/actions/cache-trust-dispatch`) maps each job to
its container, `MATHLIB_CACHE_PRIMARY`, and sets `MATHLIB_CACHE_REPO_SCOPE` to
the build SHA for the `forks` class. The upload step runs
`put-staged --container=$MATHLIB_CACHE_PRIMARY --repo=$REPO` against the
Azure storage account. The R2 leg runs the same command with `--backend=s3`
and the container's root in its bucket as `MATHLIB_CACHE_PUT_URL`. A class
moves to another store by exporting `MATHLIB_CACHE_PUT_URL` for its jobs; the
command line stays. The OIDC token, not the URL, is the write boundary (see
[`SECURITY.md`](./SECURITY.md)).

## Backends and transfer tools

`--backend` selects the storage backend: `azure` (the default) or `s3`. The
backend selects the credential variables it reads (see
[Environment variables](#environment-variables)) and the transfer tool. The
upload goes under the container's root: the URL `MATHLIB_CACHE_PUT_URL`
names, or, on the azure backend, the container on the Azure storage account.

- `azure` uploads with curl: parallel PUTs signed with the OIDC bearer token.
  A non-overwrite put skips objects the destination already holds
  (`If-None-Match: *`).
- `s3` needs `MATHLIB_CACHE_PUT_URL`, which names the bucket by path
  (`https://host/bucket[/prefix]`), and uploads with a system
  [rclone](https://rclone.org) when one works on PATH, with curl (SigV4 per
  request) otherwise. rclone receives the S3 credentials through its
  environment (`RCLONE_S3_*`) and runs 16 transfers in parallel; a
  non-overwrite put passes `--ignore-existing` in place of
  `If-None-Match: *`. Both tools upload only the command's file list.

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment.

The curl tool's non-overwrite guard relies on the store honoring
`If-None-Match: *`.

## Environment variables

| Variable | Description |
|----------|-------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure OIDC bearer token (`--backend=azure`, the default). |
| `MATHLIB_CACHE_S3_ACCESS_KEY_ID`, `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` | S3 credentials (SigV4), for `--backend=s3`. The pair must be set together. |
| `MATHLIB_CACHE_S3_SESSION_TOKEN` | Session token of a temporary S3 credential; optional. |
| `MATHLIB_CACHE_S3_REGION` | The SigV4 signing region the store expects, for `--backend=s3`. Required. |
| `MATHLIB_CACHE_PUT_URL` | The root of the `--container` write: the URL that holds the container's `f/` and `m/` trees. The azure backend defaults to the container on the Azure storage account; `--backend=s3` requires it, with the bucket named by path (`https://host/bucket[/prefix]`). |
| `MATHLIB_CACHE_PUT_FORCE_CURL` | Set to 1 or true to upload with curl on `--backend=s3`, which otherwise prefers rclone. The azure backend always uploads with curl. |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit namespace, for reads and for an upload to `forks` (see `--scope`, which takes precedence). |
| `MATHLIB_CACHE_FROM` | Container list for reads, same shape as `--cache-from`, which takes precedence. CI sets it to widen reads per job; on the canonical repo a set value selects the developer-cache workflow (see [`WORKFLOWS.md`](./WORKFLOWS.md)). |
| `MATHLIB_CACHE_BASE_URL` | Read base for both caches: a host that mirrors the whole `/{container}/{key}` namespace. Default: each cache's own endpoint. |
| `MATHLIB_CACHE_DEVELOPER_BASE_URL` | Read base for the developer cache's containers only; wins over `MATHLIB_CACHE_BASE_URL` for them. |

An empty value means unset.
