/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# The upload contract

What every upload engine consumes:

* the upload credentials (`UploadAuth`) and their resolution from the
  environment;
* the one destination resolution every upload addresses
  (`StagedUploadDest`, `stagedUploadDest`);

The engines live in `Cache/Upload/Curl.lean` and `Cache/Upload/Rclone.lean`;
`Cache/Upload.lean` selects one and dispatches. The marker path contract and
write mechanics live in `Cache/Marker.lean`. The read side
(`Cache/Requests.lean`) shares the path contract through `fileDirPath` and
`markerDirPath` (`Cache/Infra.lean`), so every upload engine addresses the
URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- Authentication method used for cache upload operations. -/
inductive UploadAuth where
  | azureBearer (token : String)
  /-- S3-compatible credentials for a direct bucket write, signed per request
  with SigV4 by curl. `sessionToken?` carries the session token of a temporary
  credential and is absent for a static keypair. -/
  | s3 (keyId secret : String) (sessionToken? : Option String)

/--
Resolve the upload credentials from the raw environment values, most specific
mechanism first:

1. S3 credentials (`MATHLIB_CACHE_S3_ACCESS_KEY_ID` /
   `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY`, plus the optional
   `MATHLIB_CACHE_S3_SESSION_TOKEN`). One of the pair without the other is a
   misconfiguration and errors rather than falling through: a fall-through
   would send the upload to a different storage backend than the one the
   half-set credentials name.
2. `MATHLIB_CACHE_AZURE_BEARER_TOKEN`.

`MATHLIB_CACHE_SAS` (`sas?`) is not an accepted credential: an environment
where it is the only value set gets an error that names the accepted
mechanisms, rather than a missing-credential error.

Pure so the precedence is testable; `getUploadAuth` wires the environment in.
-/
def uploadAuthFrom (s3KeyId? s3Secret? s3Session? bearer? sas? : Option String) :
    Except String UploadAuth :=
  match s3KeyId?, s3Secret? with
  | some keyId, some secret => .ok (.s3 keyId secret s3Session?)
  | some _, none => .error
      "MATHLIB_CACHE_S3_ACCESS_KEY_ID is set but MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is not"
  | none, some _ => .error
      "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is set but MATHLIB_CACHE_S3_ACCESS_KEY_ID is not"
  | none, none =>
    match bearer?, sas? with
    | some token, _ => .ok (.azureBearer token)
    | none, some _ => .error
        "MATHLIB_CACHE_SAS is retired: upload with the S3 credential pair or an \
        Azure OIDC bearer token (MATHLIB_CACHE_AZURE_BEARER_TOKEN)"
    | none, none => .error
        "environment variable MATHLIB_CACHE_S3_ACCESS_KEY_ID/MATHLIB_CACHE_S3_SECRET_ACCESS_KEY \
        or MATHLIB_CACHE_AZURE_BEARER_TOKEN must be set to upload caches"

/-- Retrieves upload credentials from the environment via `uploadAuthFrom`. -/
def getUploadAuth : IO UploadAuth := do
  IO.ofExcept <| uploadAuthFrom
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_ACCESS_KEY_ID")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SESSION_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_AZURE_BEARER_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_SAS")

/--
The resolved destination of a staged (`put`) upload: `base` is the upload base
the operator configured, and the prefixes are relative to it, with no trailing
slash. Every staged file is uploaded under `filesPrefix` with its base name
kept; the per-SHA marker is uploaded under `markerPrefix` with the SHA as its
name
(`fileURL`, `markerURL`). `label` names the destination in progress and
warning messages: the container name, or a note that an endpoint override
applies.
-/
structure StagedUploadDest where
  base : String
  label : String
  filesPrefix : String
  markerPrefix : String
  deriving Repr, BEq

/-- Upload URL of a staged file: `{base}/{filesPrefix}/{fileName}`. Every
engine addresses this URL (rclone through its `:s3:` remote syntax). -/
def StagedUploadDest.fileURL (dest : StagedUploadDest) (fileName : String) : String :=
  s!"{dest.base}/{dest.filesPrefix}/{fileName}"

/-- Upload URL of the per-SHA marker: `{base}/{markerPrefix}/{sha}`. Every
engine addresses this URL (rclone through its `:s3:` remote syntax). -/
def StagedUploadDest.markerURL (dest : StagedUploadDest) (sha : String) : String :=
  s!"{dest.base}/{dest.markerPrefix}/{sha}"

/--
Pure core of `stagedUploadDest`: resolve the upload base and the shared
relative prefixes for a staged set. The precedence:

1. `MATHLIB_CACHE_PUT_URL` (`putUrl?`): a flat endpoint with the container
   policy off. Any set value counts here, an empty one included: a
   misconfigured endpoint fails the upload rather than divert it to the
   fallback below. The read variables take the opposite rule, where an empty
   value means unset.
2. `MATHLIB_CACHE_PUT_BASE_URL` (`putBase?`, empty means unset): rebases the
   chosen container's write under the given host, as `MATHLIB_CACHE_BASE_URL`
   rebases reads. CI uses it to select the upload storage. It requires
   `--container`, since a base rebases a container write.
3. The Azure account, for the chosen container.
4. With none of them, the `legacy` container on the Azure account; the IO
   wrapper warns.

The prefixes build on `fileDirPath` and `markerDirPath`, the same policies
the reads use, so every upload path follows the read-side path contract.
-/
def stagedUploadDestFrom (putUrl? putBase? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String StagedUploadDest :=
  if let some url := putUrl? then
    -- A user-supplied URL carries no container policy; the prefix follows the
    -- repo alone, flat for `MATHLIBREPO` and repo-namespaced otherwise.
    .ok { base := url, label := "(env override)",
          filesPrefix := fileDirPath none repo scope?,
          markerPrefix := markerDirPath repo }
  else
    let containerDest (base : String) (c : Container) : StagedUploadDest :=
      { base, label := c.name,
        filesPrefix := s!"{c.pathSegment}/{fileDirPath (some c) repo scope?}",
        markerPrefix := s!"{c.pathSegment}/{markerDirPath repo}" }
    match normalizeBaseURL putBase?, container? with
    | some base, some c => .ok (containerDest base c)
    | some _, none => .error
        "MATHLIB_CACHE_PUT_BASE_URL is set, which rebases a container write; \
        pass --container=NAME to name the container."
    | none, some c => .ok (containerDest azureAccountURL c)
    | none, none => .ok (containerDest azureAccountURL .legacy)

/--
`stagedUploadDestFrom`, resolved from the environment. The one destination
resolution every upload consumes: the artifact puts and the marker put, on
every engine, address `{base}/{prefix}/{name}`.
-/
def stagedUploadDest (container? : Option Container) (repo : String) :
    IO StagedUploadDest := do
  let putUrl? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let putBase? ← IO.getEnv "MATHLIB_CACHE_PUT_BASE_URL"
  if putUrl?.isNone && (normalizeBaseURL putBase?).isNone && container?.isNone then
    IO.eprintln <|
      "Warning: cache upload without --container=NAME; defaulting to the\n" ++
      "         `legacy` (bare `mathlib4`) container. Pass --container=NAME\n" ++
      "         explicitly to choose a trust-level container."
  IO.ofExcept <| stagedUploadDestFrom putUrl? putBase? container? repo (← getRepoScope)

end Cache.Requests
