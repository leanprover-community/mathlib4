/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# The S3 backend

The upload logic specific to an S3-compatible backend; the production S3
backend is Cloudflare R2. This module holds:

* the credential set (`S3Credentials`);
* the SigV4 curl arguments (`s3CurlArgs`);
* the backend configuration for the rclone tool (`rcloneEnv`);
* the endpoint and bucket addressing rclone needs (`s3EndpointSplit`).
-/

namespace Cache.Requests

/-- S3-compatible credentials for a direct bucket write. `sessionToken?`
carries the session token of a temporary credential and is absent for a
static keypair. -/
structure S3Credentials where
  keyId : String
  secret : String
  sessionToken? : Option String
  deriving DecidableEq, Repr, BEq

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
rclone addresses a destination as `:s3:{bucket}/{key}` against an endpoint,
so a base without a bucket path cannot take the rclone tool.
-/
def s3EndpointSplit (base : String) : Except String (String × String) :=
  match base.splitOn "://" with
  | [scheme, rest] =>
    match rest.splitOn "/" with
    | host :: parts =>
      if host.isEmpty || parts.isEmpty || parts.any (·.isEmpty) then
        .error s!"the upload base '{base}' does not name a bucket \
          (the rclone tool needs https://endpoint/bucket)"
      else
        .ok (s!"{scheme}://{host}", "/".intercalate parts)
    | [] => .error s!"the upload base '{base}' is not a URL"
  | _ => .error s!"the upload base '{base}' is not a URL"

/--
The rclone S3 backend configuration. It travels in the child environment, so
no credential reaches a command line. `RCLONE_S3_SESSION_TOKEN` is set for a
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

end Cache.Requests
