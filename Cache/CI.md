# Mathlib cache: CI uploads

The upload logic in `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it. External consumers should not depend
on them.

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
| `--container=NAME`  | The target container: `master` or `forks`. Required on `--backend=s3` unless `MATHLIB_CACHE_PUT_URL` is set. |
| `--backend=NAME`    | The storage backend, `s3` (the default) or `azure` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload.   |
| `--scope=REF`       | The per-commit namespace to upload under, and its completeness marker. Takes precedence over `MATHLIB_CACHE_REPO_SCOPE`. The read-side use of `--scope` is documented in the README. |

## Backends and transfer tools

The backend selects the destination, the credential variables it reads (see
[Environment variables](#environment-variables)), and the transfer tool:

- `s3` writes to the bucket endpoint `MATHLIB_CACHE_PUT_BASE_URL` names
  (`https://host/bucket`) and uploads with a system
  [rclone](https://rclone.org) when one works on PATH, with curl (SigV4 per
  request) otherwise. rclone receives the S3 credentials through its
  environment (`RCLONE_S3_*`) and runs 16 transfers in parallel; a
  non-overwrite put passes `--ignore-existing` in place of
  `If-None-Match: *`. Both tools upload only the command's file list.
- `azure` writes only to the flat endpoint `MATHLIB_CACHE_PUT_URL` names. It
  uploads with curl: parallel PUTs signed with the OIDC bearer token. A
  non-overwrite put skips objects the destination already holds
  (`If-None-Match: *`).

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment.

The curl tool's non-overwrite guard relies on the store honoring
`If-None-Match: *`.

## Environment variables

| Variable | Description |
|----------|-------------|
| `MATHLIB_CACHE_AZURE_BEARER_TOKEN` | Azure OIDC bearer token, for `--backend=azure`. |
| `MATHLIB_CACHE_S3_ACCESS_KEY_ID`, `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` | S3 credentials (SigV4), for `--backend=s3`. The pair must be set together. |
| `MATHLIB_CACHE_S3_SESSION_TOKEN` | Session token of a temporary S3 credential; optional. |
| `MATHLIB_CACHE_S3_REGION` | The SigV4 signing region the store expects, for `--backend=s3`. Required. |
| `MATHLIB_CACHE_PUT_BASE_URL` | The upload base for `--backend=s3`: the bucket endpoint (`https://host/bucket`). The `--container` upload goes to `{base}/{container}/{key}` and keeps the container path policy. Required unless `MATHLIB_CACHE_PUT_URL` is set. |
| `MATHLIB_CACHE_PUT_URL` | Upload to this single URL as a flat namespace, on either backend. On `--backend=s3` it must name the bucket by path (`https://host/bucket[/prefix]`). Required for `--backend=azure`. |
| `MATHLIB_CACHE_PUT_FORCE_CURL` | Set to 1 or true to upload with curl on `--backend=s3`, which otherwise prefers rclone. |
| `MATHLIB_CACHE_REPO_SCOPE` | The per-commit namespace, for reads and `put` (see `--scope`, which takes precedence). |
| `MATHLIB_CACHE_FROM` | Container list for reads, same shape as `--cache-from`, which takes precedence. CI sets it to widen reads per job. |

An empty value means unset for every variable above except
`MATHLIB_CACHE_PUT_URL`, where any set value counts: a misconfigured endpoint
fails the upload and does not divert it to the backend's destination.
