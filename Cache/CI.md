# Mathlib cache: CI uploads

The upload logic in `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it. External consumers should not depend
on them.

The trust model behind the containers and the write credentials is in [`SECURITY.md`](./SECURITY.md).

## Upload commands

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `put`       | Run `pack`, then upload the files this build links from the local cache. The build graph limits the upload to those files. A `--scope` adds a per-commit namespace and marker on `forks`. |
| `put!`      | Same as `put`, overwriting files the server already holds             |
| `put-staged`| Upload the `*.ltar` files in `--staging-dir` to the resolved location. CI uploads with this command; `--backend` selects the storage backend. |

## Upload options

| Option              | Description                                          |
|---------------------|------------------------------------------------------|
| `--container=NAME`  | The target container: `master` or `forks`. Required. The container decides the layout under its root: flat (`f/{hash}.ltar`) for `master`, repo-namespaced (`f/{repo}/{hash}.ltar`) for `forks`, and with a scope the per-commit namespace (`f/{repo}/{sha}/{hash}.ltar`) of `forks`. |
| `--backend=NAME`    | The storage backend, `s3` (the default) or `azure` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload.   |
| `--scope=REF`       | The per-commit namespace to upload under, and its completeness marker. Only `forks` has per-commit namespaces; a scope on `master` is an error. Takes precedence over `MATHLIB_CACHE_REPO_SCOPE`. The read-side use of `--scope` is documented in [`WORKFLOWS.md`](./WORKFLOWS.md). |

`lake exe cache <command> --help` lists the flags of each command.

## Backends and transfer tools

The backend determines the credential variables (see
[Environment variables](#environment-variables)) and the transfer tool. The
upload goes under the container's root, the URL `MATHLIB_CACHE_PUT_URL` names,
on every backend:

- `s3` needs the URL to name the bucket by path
  (`https://host/bucket[/prefix]`), and uploads with a system
  [rclone](https://rclone.org) when one works on PATH, with curl (SigV4 per
  request) otherwise. rclone receives the S3 credentials through its
  environment (`RCLONE_S3_*`) and runs 16 transfers in parallel; a
  non-overwrite put passes `--ignore-existing` in place of
  `If-None-Match: *`. Both tools upload only the command's file list.
- `azure` uploads with curl: parallel PUTs signed with the OIDC bearer token.
  A non-overwrite put skips objects that already exist at the destination
  (`If-None-Match: *`).

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment.

The curl tool's non-overwrite guard relies on the store honoring
`If-None-Match: *`. The jobs that run the tool on a GitHub runner install a
pinned curl release from [static-curl](https://github.com/leanprover-community/static-curl).

## Environment variables

| Variable | Description |
|----------|-------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure OIDC bearer token, for `--backend=azure`. |
| `MATHLIB_CACHE_S3_ACCESS_KEY_ID`, `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` | S3 credentials (SigV4), for `--backend=s3`. The pair must be set together. |
| `MATHLIB_CACHE_S3_SESSION_TOKEN` | Session token of a temporary S3 credential; optional. |
| `MATHLIB_CACHE_S3_REGION` | The SigV4 signing region the store expects, for `--backend=s3`. Required. |
| `MATHLIB_CACHE_PUT_URL` | The root of the `--container` write: the URL that holds the container's `f/` and `m/` trees. Required on every backend. On `--backend=s3` the URL must include the bucket in its path (`https://host/bucket[/prefix]`). |
| `MATHLIB_CACHE_PUT_FORCE_CURL` | Set to 1 or true to upload with curl on `--backend=s3`. Otherwise the tool uses rclone when it is available. |
| `MATHLIB_CACHE_PARALLEL_MAX` | The parallel curl transfer limit for uploads and downloads (50 by default). |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit namespace for reads and `forks` uploads (see `--scope`, which takes precedence). The trust dispatch sets it for every fork-trust build; on the canonical repo a set value selects the developer-cache workflow (see [`WORKFLOWS.md`](./WORKFLOWS.md)). |
| `MATHLIB_CACHE_FROM` | Container list for reads, same shape as `--cache-from`, which takes precedence. On the canonical repo a set value selects the developer-cache workflow. |

An empty value means unset for every variable above.
