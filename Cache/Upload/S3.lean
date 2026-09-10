/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Dest
import Cache.Upload.Curl
import Cache.Upload.Rclone

/-!
# The S3 backend

The complete s3 upload path; the production S3 backend is Cloudflare R2.
This module holds:

* the credential set (`S3Credentials`) and its resolution (`s3AuthFrom`);
* the destination resolution (`s3UploadDestFrom`);
* the transfer-tool policy (`s3UploadToolFrom`);
* the SigV4 curl arguments (`s3CurlArgs`);
* the rclone tool's configuration (`rcloneEnv`) and the endpoint and bucket
  addressing it needs (`s3EndpointSplit`);
* the transfer entry point (`s3PutStaged`).
-/

namespace Cache.Requests

open System (FilePath)

/--
The upload destination for the s3 backend: the container write rebased under
the bucket endpoint `MATHLIB_CACHE_PUT_BASE_URL` names (`putBase?`), as
`MATHLIB_CACHE_BASE_URL` rebases reads. A bucket URL is account-specific, so
the backend has no default endpoint and an unset base errors. A base without
`--container` errors, since a base rebases a container write.
-/
def s3UploadDestFrom (putBase? : Option String) (container? : Option Container)
    (repo : String) (scope? : Option String) : Except String StagedUploadDest :=
  match putBase?, container? with
  | some base, some c => .ok (containerUploadDest base c repo scope?)
  | some _, none => .error
      "MATHLIB_CACHE_PUT_BASE_URL is set, which rebases a container write; \
      pass --container=NAME to name the container."
  | none, _ => .error
      "the s3 backend uploads to the bucket endpoint MATHLIB_CACHE_PUT_BASE_URL \
      names (https://host/bucket): set it, or set MATHLIB_CACHE_PUT_URL for a \
      flat upload"

/-- S3-compatible credentials for a direct bucket write. `sessionToken?`
carries the session token of a temporary credential and is absent for a
static keypair. -/
structure S3Credentials where
  keyId : String
  secret : String
  sessionToken? : Option String
  deriving DecidableEq, Repr, BEq

/--
The s3 upload credentials, from the raw environment values:
`MATHLIB_CACHE_S3_ACCESS_KEY_ID` and `MATHLIB_CACHE_S3_SECRET_ACCESS_KEY`
(`keyId?`, `secret?`), plus the optional `MATHLIB_CACHE_S3_SESSION_TOKEN`
(`session?`). One of the pair without the other is a misconfiguration and
errors.

Pure so the policy is testable; `getS3Auth` wires the environment in.
-/
def s3AuthFrom (keyId? secret? session? : Option String) :
    Except String S3Credentials :=
  match keyId?, secret? with
  | some keyId, some secret => .ok ⟨keyId, secret, session?⟩
  | some _, none => .error
      "MATHLIB_CACHE_S3_ACCESS_KEY_ID is set but MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is not"
  | none, some _ => .error
      "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY is set but MATHLIB_CACHE_S3_ACCESS_KEY_ID is not"
  | none, none => .error
      "--backend=s3 uploads with the S3 credential pair: set \
      MATHLIB_CACHE_S3_ACCESS_KEY_ID and MATHLIB_CACHE_S3_SECRET_ACCESS_KEY"

/-- Retrieves the s3 upload credentials from the environment via
`s3AuthFrom`. -/
def getS3Auth : IO S3Credentials := do
  IO.ofExcept <| s3AuthFrom
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_ACCESS_KEY_ID")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SESSION_TOKEN")

/--
The curl arguments for an upload signed with S3 credentials. curl signs each
request with SigV4 (`--aws-sigv4`); region `auto` fits R2. The
`x-amz-content-sha256: UNSIGNED-PAYLOAD` header lets curl sign a `-T` file
upload; curl supports this from 7.87, and this path runs in CI, whose runners
ship newer curls. A temporary credential also sends its session token, which
SigV4 covers as an `x-amz-*` header. The argument list carries the secrets,
so callers print curl failures without the argument list.
-/
def s3CurlArgs (creds : S3Credentials) : Array String :=
  let sessionArgs : Array String := match creds.sessionToken? with
    | some token => #["-H", s!"x-amz-security-token: {token}"]
    | none => #[]
  #["--aws-sigv4", "aws:amz:auto:s3", "--user", s!"{creds.keyId}:{creds.secret}",
    "-H", "x-amz-content-sha256: UNSIGNED-PAYLOAD"] ++ sessionArgs

/--
Split an S3 upload base into the endpoint origin and the bucket path:
`https://host/bucket[/prefix]` becomes `(https://host, bucket[/prefix])`.
rclone addresses a destination as `:s3:{bucket}/{key}` against an endpoint.
`stagedUploadDestFrom` rejects an s3 base that does not split.
-/
def s3EndpointSplit (base : String) : Except String (String × String) :=
  match base.splitOn "://" with
  | [scheme, rest] =>
    match rest.splitOn "/" with
    | host :: parts =>
      if host.isEmpty || parts.isEmpty || parts.any (·.isEmpty) then
        .error s!"the upload base '{base}' does not name a bucket \
          (the s3 backend needs https://endpoint/bucket)"
      else
        .ok (s!"{scheme}://{host}", "/".intercalate parts)
    | [] => .error s!"the upload base '{base}' is not a URL"
  | _ => .error s!"the upload base '{base}' is not a URL"

/--
The rclone S3 backend configuration. It is passed in the child environment,
so no credential appears on a command line. `RCLONE_S3_SESSION_TOKEN` is set for a
temporary credential and cleared otherwise, so a stale token in the caller's
environment is not inherited. Region `auto` matches the curl tool's SigV4
region. rclone refuses to run without a provider, so `provider` must carry
one; `putStagedViaRclone` keeps the caller's `RCLONE_S3_PROVIDER` and
defaults to the generic `Other`. Every other `RCLONE_S3_*` option inherits
from the caller, so an operator can tune transfers without a code change.
-/
def rcloneEnv (creds : S3Credentials) (endpoint provider : String) :
    Array (String × Option String) :=
  #[("RCLONE_S3_ENV_AUTH", some "false"),
    ("RCLONE_S3_ACCESS_KEY_ID", some creds.keyId),
    ("RCLONE_S3_SECRET_ACCESS_KEY", some creds.secret),
    ("RCLONE_S3_SESSION_TOKEN", creds.sessionToken?),
    ("RCLONE_S3_ENDPOINT", some endpoint),
    ("RCLONE_S3_PROVIDER", some provider),
    ("RCLONE_S3_REGION", some "auto")]

/-- The transfer tool an s3 upload uses. -/
inductive S3UploadTool where
  | curl
  | rclone
  deriving DecidableEq, Repr

/--
The transfer tool for an s3 upload: rclone when one works on PATH, curl
otherwise. `forceCurl` (the `MATHLIB_CACHE_PUT_FORCE_CURL` flag) selects curl
regardless.

Pure so the policy is testable; `s3PutStaged` wires the environment in.
-/
def s3UploadToolFrom (forceCurl rcloneAvailable : Bool) : S3UploadTool :=
  if !forceCurl && rcloneAvailable then .rclone else .curl

/--
The staged put on the s3 backend: resolve the transfer tool
(`s3UploadToolFrom`) and transfer, each request signed with `creds`. Only
this resolution reads the `MATHLIB_CACHE_PUT_FORCE_CURL` flag, and the
availability probe runs only when the flag does not already force curl. The
rclone tool receives the credentials through its child environment
(`rcloneEnv`), with the endpoint and bucket split from the destination base
(`s3EndpointSplit`) and the provider from the caller's `RCLONE_S3_PROVIDER`
(the generic `Other` when unset).
-/
def s3PutStaged (dest : StagedUploadDest) (creds : S3Credentials) (srcDir : FilePath)
    (fileNames : Array String) (overwrite : Bool) (markerSha? : Option String) :
    IO Unit := do
  let (endpoint, bucketPath) ← IO.ofExcept (s3EndpointSplit dest.base)
  let forceCurl ← getEnvFlag "MATHLIB_CACHE_PUT_FORCE_CURL" (ifUnset := false)
  let available ← if forceCurl then pure false else rcloneAvailable
  match s3UploadToolFrom forceCurl available with
  | .curl =>
    putStagedViaCurl dest (pure (s3CurlArgs creds)) srcDir fileNames overwrite markerSha?
  | .rclone =>
    let provider := (← getEnvNonEmpty "RCLONE_S3_PROVIDER").getD "Other"
    putStagedViaRclone dest (rcloneEnv creds endpoint provider) bucketPath
      markerSha? srcDir fileNames overwrite

end Cache.Requests
