/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker
import Cache.Upload.Azure
import Cache.Upload.S3

/-!
# The upload contract

The backend-neutral layer every upload tool consumes:

* the backend selection (`UploadBackend`) and the upload credentials
  (`UploadAuth`) with their resolution from the environment. The resolution
  arbitrates between the storage backends; the backend mechanics live in
  `Cache/Upload/Azure.lean` and `Cache/Upload/S3.lean`;
* the one destination resolution every upload addresses
  (`stagedUploadDest`): the flat `MATHLIB_CACHE_PUT_URL` override, or the
  selected backend's own destination. The destination contract itself
  (`StagedUploadDest`) lives in `Cache/Upload/Dest.lean`.

The tools live in `Cache/Upload/Curl.lean` and `Cache/Upload/Rclone.lean`;
`Cache/Upload.lean` selects one and dispatches. The marker path contract and
write mechanics live in `Cache/Marker.lean`. The read side
(`Cache/Requests.lean`) shares the path contract through `fileDirPath` and
`markerDirPath` (`Cache/Infra.lean`), so every upload tool addresses the
URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- The storage backend an upload targets, selected with `--backend=NAME`.
The backend decides which credentials sign the upload (`uploadAuthFrom`) and
which transfer tool moves the bytes (`resolveUploadTool`). -/
inductive UploadBackend where
  /-- Azure Blob Storage (`Cache/Upload/Azure.lean`); the default. -/
  | azure
  /-- An S3-compatible bucket (`Cache/Upload/S3.lean`); Cloudflare R2 in
  production. -/
  | s3
  deriving DecidableEq, Repr, BEq, Inhabited

namespace UploadBackend

/-- Canonical short name for a backend, used in the `--backend` flag. -/
def name : UploadBackend → String
  | .azure => "azure"
  | .s3    => "s3"

/-- All known backends, listed in their canonical declaration order. -/
def all : List UploadBackend := [.azure, .s3]

/-- Parse a short name back into an `UploadBackend`. Matching is
case-insensitive. -/
def parse? (s : String) : Option UploadBackend :=
  match s.toLower with
  | "azure" => some .azure
  | "s3"    => some .s3
  | _       => none

end UploadBackend

/-- The authentication mechanism for cache uploads, one constructor per
storage backend. This type carries the resolved credentials the backend
modules sign with. -/
inductive UploadAuth where
  /-- An Azure OAuth bearer token (`Cache/Upload/Azure.lean`). -/
  | azureBearer (token : String)
  /-- S3-compatible credentials for a direct bucket write
  (`Cache/Upload/S3.lean`). -/
  | s3 (creds : S3Credentials)

/--
Resolve the upload credentials for the selected `backend` from the raw
environment values. Each backend reads only its own variables:

* `azure`: `MATHLIB_CACHE_AZURE_BEARER_TOKEN` (`bearer?`).
* `s3`: `MATHLIB_CACHE_S3_ACCESS_KEY_ID` and
  `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY` (`s3KeyId?`, `s3Secret?`), plus the
  optional `MATHLIB_CACHE_S3_SESSION_TOKEN` (`s3Session?`). One of the pair
  without the other is a misconfiguration and errors.

`MATHLIB_CACHE_SAS` (`sas?`) is not an accepted credential: on the `azure`
backend, when it is set and the bearer token is not, the error names the
accepted mechanism instead of reporting a missing credential.

Pure so the policy is testable; `getUploadAuth` wires the environment in.
-/
def uploadAuthFrom (backend : UploadBackend)
    (s3KeyId? s3Secret? s3Session? bearer? sas? : Option String) :
    Except String UploadAuth :=
  match backend with
  | .s3 =>
    match s3KeyId?, s3Secret? with
    | some keyId, some secret => .ok (.s3 ⟨keyId, secret, s3Session?⟩)
    | some _, none => .error
        "MATHLIB_CACHE_S3_ACCESS_KEY_ID is set but MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is not"
    | none, some _ => .error
        "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is set but MATHLIB_CACHE_S3_ACCESS_KEY_ID is not"
    | none, none => .error
        "--backend=s3 uploads with the S3 credential pair: set \
        MATHLIB_CACHE_S3_ACCESS_KEY_ID and MATHLIB_CACHE_S3_SECRET_ACCESS_KEY"
  | .azure =>
    match bearer?, sas? with
    | some token, _ => .ok (.azureBearer token)
    | none, some _ => .error
        "MATHLIB_CACHE_SAS is retired: set an Azure OIDC bearer token \
        (MATHLIB_CACHE_AZURE_BEARER_TOKEN), or pass --backend=s3 to upload \
        with the S3 credential pair"
    | none, none => .error
        "the azure backend (the default) uploads with an Azure OIDC bearer token: \
        set MATHLIB_CACHE_AZURE_BEARER_TOKEN, or pass --backend=s3 to upload \
        with the S3 credential pair"

/-- Retrieves the upload credentials for `backend` from the environment via
`uploadAuthFrom`. -/
def getUploadAuth (backend : UploadBackend) : IO UploadAuth := do
  IO.ofExcept <| uploadAuthFrom backend
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_ACCESS_KEY_ID")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SESSION_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_AZURE_BEARER_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_SAS")

/--
Pure core of `stagedUploadDest`: resolve where a staged set uploads.

`MATHLIB_CACHE_PUT_URL` (`putUrl?`) wins on every backend: a flat endpoint
with the container policy off; the selected backend still signs the requests.
Any set value counts here, an empty one included: a misconfigured endpoint
fails the upload and does not divert it to the backend's destination. The
read variables take the opposite rule, where an empty value means unset.

Without it, the backend resolves its own destination — `azureUploadDestFrom`
(the Azure account) or `s3UploadDestFrom` (the bucket endpoint
`MATHLIB_CACHE_PUT_BASE_URL` names; `putBase?`, empty means unset).
-/
def stagedUploadDestFrom (backend : UploadBackend) (putUrl? putBase? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String StagedUploadDest :=
  if let some url := putUrl? then
    -- A user-supplied URL carries no container policy; the prefix follows the
    -- repo alone, flat for `MATHLIBREPO` and repo-namespaced otherwise.
    .ok { base := url, label := "(env override)",
          filesPrefix := fileDirPath none repo scope?,
          markerPrefix := markerDirPath repo }
  else
    let putBase? := normalizeBaseURL putBase?
    match backend with
    | .azure => azureUploadDestFrom putBase? container? repo scope?
    | .s3 => s3UploadDestFrom putBase? container? repo scope?

/--
`stagedUploadDestFrom`, resolved from the environment. The one destination
resolution every upload consumes: the artifact puts and the marker put, on
every tool, address `{base}/{prefix}/{name}`. The warning covers the azure
backend's `legacy` fallback; the s3 backend never falls back — without a
destination it errors.
-/
def stagedUploadDest (backend : UploadBackend) (container? : Option Container)
    (repo : String) : IO StagedUploadDest := do
  let putUrl? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let putBase? ← IO.getEnv "MATHLIB_CACHE_PUT_BASE_URL"
  if backend == .azure && putUrl?.isNone && (normalizeBaseURL putBase?).isNone
      && container?.isNone then
    IO.eprintln <|
      "Warning: cache upload without --container=NAME; defaulting to the\n" ++
      "         `legacy` (bare `mathlib4`) container. Pass --container=NAME\n" ++
      "         explicitly to choose a trust-level container."
  IO.ofExcept <| stagedUploadDestFrom backend putUrl? putBase? container? repo (← getRepoScope)

end Cache.Requests
