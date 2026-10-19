# Mathlib cache: CI uploads

The upload logic in `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it. External consumers should not depend
on them.

The trust model behind the containers and the write credentials is in [`SECURITY.md`](./SECURITY.md).

## Upload commands

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `put`       | Run `pack`, then upload the files this build links from the local cache. The build graph limits the upload to those files. A `--scope` adds a per-commit namespace and marker when the destination uses repo scopes. |
| `put!`      | Same as `put`, overwriting files the server already holds             |
| `put-staged`| Upload the `*.ltar` files in `--staging-dir` to the resolved destination. CI uploads with this command; `--backend` selects the storage backend. |

## Upload options

| Option              | Description                                          |
|---------------------|------------------------------------------------------|
| `--container=NAME`  | The target container: `master` or `forks`. Required on `--backend=s3` unless `MATHLIB_CACHE_PUT_URL` is set, in which case it is ignored. Rejected on `--backend=azure`. |
| `--backend=NAME`    | The storage backend, `s3` (the default) or `azure` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload.   |
| `--scope=REF`       | The per-commit namespace and marker for repo-scoped destinations. Flat destinations ignore it. Takes precedence over `MATHLIB_CACHE_REPO_SCOPE`. The read-side use of `--scope` is documented in the README. |

## Backends and transfer tools

The backend determines the destination, the credential variables (see
[Environment variables](#environment-variables)), and the transfer tool:

- `s3` writes to the bucket endpoint `MATHLIB_CACHE_PUT_BASE_URL` names
  (`https://host/bucket`) and uploads with a system
  [rclone](https://rclone.org) when one works on PATH, with curl (SigV4 per
  request) otherwise. rclone receives the S3 credentials through its
  environment (`RCLONE_S3_*`) and runs 16 transfers in parallel; a
  non-overwrite put passes `--ignore-existing` in place of
  `If-None-Match: *`. Both tools upload only the command's file list.
- `azure` writes only through `MATHLIB_CACHE_PUT_URL`, without a container
  segment. The tool uploads with curl: parallel PUTs signed with the OIDC
  bearer token. A non-overwrite put skips objects that already exist at the
  destination (`If-None-Match: *`).

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment.

The curl tool's non-overwrite guard relies on the store honoring
`If-None-Match: *`. Parallel curl uploads use `MATHLIB_CACHE_PARALLEL_MAX`
transfers (50 by default).

## Environment variables

| Variable | Description |
|----------|-------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure OIDC bearer token, for `--backend=azure`. |
| `MATHLIB_CACHE_S3_ACCESS_KEY_ID`, `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` | S3 credentials (SigV4), for `--backend=s3`. The pair must be set together. |
| `MATHLIB_CACHE_S3_SESSION_TOKEN` | Session token of a temporary S3 credential; optional. |
| `MATHLIB_CACHE_S3_REGION` | The SigV4 signing region the store expects, for `--backend=s3`. Required. |
| `MATHLIB_CACHE_PUT_BASE_URL` | The upload base for `--backend=s3`: the bucket endpoint (`https://host/bucket`). The tool writes the `--container` files to `{base}/{container}/{key}` and keeps the container path policy. Required unless `MATHLIB_CACHE_PUT_URL` is set. |
| `MATHLIB_CACHE_PUT_URL` | Upload under this URL without a container segment. The canonical repo uses a flat file layout; other repos use a repo scope and can write a commit marker. On `--backend=s3` the URL must include the bucket in its path (`https://host/bucket[/prefix]`). Required for `--backend=azure`. |
| `MATHLIB_CACHE_PUT_FORCE_CURL` | Set to 1 or true to upload with curl on `--backend=s3`. Otherwise the tool uses rclone when it is available. |
| `MATHLIB_CACHE_PARALLEL_MAX` | The parallel curl transfer limit for uploads and downloads (50 by default). |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit namespace for reads and repo-scoped uploads (see `--scope`, which takes precedence). Flat locations ignore it. |
| `MATHLIB_CACHE_FROM` | Container list for reads, same shape as `--cache-from`, which takes precedence. CI sets it to widen reads per job. |

An empty value means unset for every variable above except
`MATHLIB_CACHE_PUT_URL`, where any set value counts: a misconfigured endpoint
fails the upload and does not divert it to the backend's destination.
