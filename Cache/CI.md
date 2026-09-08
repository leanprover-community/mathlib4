# Mathlib cache: the CI upload path

The upload half of `lake exe cache` is internal to mathlib CI: the commands,
the backends, and their credential and destination variables follow the CI
storage layout and can change with it. An external cache should not build on
them; see
[Operating an external cache](./README.md#operating-an-external-cache) in the
README. The trust model behind the containers and the write credentials is in
[`SECURITY.md`](./SECURITY.md).

## Upload commands

| Command     | Description                                                          |
|-------------|----------------------------------------------------------------------|
| `put`       | Run `pack`, then upload the files this build links from the local cache. The build graph scopes the upload: nothing else in the shared per-user cache directory leaves the machine. A `--scope` adds the per-commit namespace and its completeness marker. |
| `put!`      | Same as `put`, overwriting files the server already holds             |
| `put-staged`| Upload the `*.ltar` files in `--staging-dir` to the selected `--container`. CI uploads with this command; `--backend` selects the storage backend. |

The upload commands write with the same URL construction `get` reads, so
uploads and reads follow one path contract. Uploading needs a writer
credential in the environment; see the environment variables in
`lake exe cache --help`.

## Upload options

| Option              | Description                                          |
|---------------------|------------------------------------------------------|
| `--container=NAME`  | The target container: `master`, `forks`, `nightly-testing`, `pr-toolchain-tests`, `legacy`. An upload targets exactly one container. |
| `--backend=NAME`    | The storage backend, `azure` (the default) or `s3` (see [Backends and transfer tools](#backends-and-transfer-tools)). |
| `--staging-dir=DIR` | For `put-staged`: the staging directory to upload.   |

## Backends and transfer tools

`--backend` selects the storage backend: `azure` (the default) or `s3`. The
backend selects the destination, the credential variables it reads (see
`lake exe cache --help`), and the transfer tool:

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

`MATHLIB_CACHE_PUT_URL` overrides the destination on either backend: one flat
endpoint, with the container policy off.

`MATHLIB_CACHE_PUT_FORCE_CURL=1` makes the `s3` backend upload with curl even
when rclone is available.

The cache binary sets the rclone credentials, endpoint, provider (`Other`
unless the environment names one), and region; every other `RCLONE_S3_*`
option inherits from the environment, so an operator can set
`RCLONE_S3_PROVIDER=Cloudflare` without a code change.
