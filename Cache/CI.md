# Mathlib cache: CI uploads

The upload logic in `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it.

External consumers should not depend on the below options as their existence and behavior might change without notice.

The trust model behind the containers and the write credentials is in [`SECURITY.md`](./SECURITY.md).

## Upload commands

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `put`       | Run `pack`, then upload the files this build links from the local cache. The build graph scopes the upload: nothing else in the shared per-user cache directory is uploaded. A `--scope` adds the per-commit namespace and its completeness marker. |
| `put!`      | Same as `put`, overwriting files the server already holds             |
| `put-staged`| Upload the `*.ltar` files in `--staging-dir` to the selected `--container`. CI uploads with this command; `--backend` selects the storage backend. |

## Upload options

| Option              | Description                                          |
|---------------------|------------------------------------------------------|
| `--container=NAME`  | The target container: `master`, `forks`, `nightly-testing`, `pr-toolchain-tests`, `legacy`. An upload targets exactly one container. Without it (and without `MATHLIB_CACHE_PUT_URL`), the azure backend falls back to `legacy` and warns. |
| `--backend=NAME`    | The storage backend, `azure` (the default) or `s3` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload.   |
| `--scope=REF`       | The per-commit namespace to upload under, followed by its completeness marker. Takes precedence over `MATHLIB_CACHE_REPO_SCOPE`. The read-side use of `--scope` is documented in the README. |

## Backends and transfer tools

`--backend` selects the storage backend: `azure` (the default) or `s3`. The
backend selects the destination, the credential variables it reads (see
[Environment variables](#environment-variables)), and the transfer tool:

- `azure` writes to the Azure storage account and uploads with curl:
  parallel PUTs, each signed per request with the OIDC bearer token; an
  upload never replaces an existing object (`If-None-Match: *`).
- `s3` writes to the bucket endpoint `MATHLIB_CACHE_PUT_BASE_URL` names
  (`https://host/bucket`) and uploads with a system
  [rclone](https://rclone.org) when one works on PATH, with curl (SigV4 per
  request) otherwise. rclone receives the S3 credentials through its
  environment (`RCLONE_S3_*`), and both tools restrict the transfer to the
  command's file list, so `put`'s build-scoped guarantee holds either way.
  rclone schedules transfers for large staged sets and verifies each
  object's checksum after upload; `--ignore-existing` replaces
  `If-None-Match` on a non-overwrite put.

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment.

## Environment variables

| Variable | Description |
|----------|-------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure OIDC bearer token (`--backend=azure`, the default). |
| `MATHLIB_CACHE_S3_ACCESS_KEY_ID`, `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` | S3 credentials (SigV4), for `--backend=s3`. The pair must be set together. |
| `MATHLIB_CACHE_S3_SESSION_TOKEN` | Session token of a temporary S3 credential; optional. |
| `MATHLIB_CACHE_PUT_BASE_URL` | The s3 backend's bucket endpoint (`https://host/bucket`). The `--container` write is rebased under it (`{base}/{container}/{key}`) and keeps the container path policy. Required for `--backend=s3` unless `MATHLIB_CACHE_PUT_URL` is set. The azure backend writes to the Azure storage account and rejects a set value. |
| `MATHLIB_CACHE_PUT_URL` | Upload to this single URL as a flat namespace, on either backend: the container policy is off, and the selected backend signs the requests. |
| `MATHLIB_CACHE_PUT_FORCE_CURL` | Set to 1 or true to upload with curl on `--backend=s3`, which otherwise prefers rclone. The azure backend always uploads with curl. |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit namespace, for reads and `put` (see `--scope`, which takes precedence). |
| `MATHLIB_CACHE_FROM` | Container list for reads, same shape as `--cache-from`, which takes precedence. CI sets it to widen reads per job. |

An empty value means unset for every variable above except
`MATHLIB_CACHE_PUT_URL`, where any set value counts: a misconfigured endpoint
fails the upload and does not divert it to the backend's destination.
