/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

/-!
# The S3 backend

Everything specific to uploading against an S3-compatible backend —
Cloudflare R2 in production: the credential set (`S3Credentials`), per-request
SigV4 signing on the curl engine (`s3CurlArgs`), the backend configuration the
rclone engine receives through its environment (`rcloneEnv`), and the
endpoint/bucket addressing rclone needs (`s3EndpointSplit`).
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
The curl arguments for an upload signed with S3 credentials: SigV4 per request
(`--aws-sigv4`; region `auto` fits R2). The explicit
`x-amz-content-sha256: UNSIGNED-PAYLOAD` header is what lets curl sign a `-T`
file upload (supported from curl 7.87); this path runs in CI, whose runners
ship newer curls. A temporary credential also sends its session token, which
SigV4 covers as an `x-amz-*` header. The secrets are passed in the argument
list; callers therefore print curl failures without their argument lists.
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
so a base without a bucket path cannot take the rclone engine.
-/
def s3EndpointSplit (base : String) : Except String (String × String) :=
  match base.splitOn "://" with
  | [scheme, rest] =>
    match rest.splitOn "/" with
    | host :: parts =>
      if host.isEmpty || parts.isEmpty || parts.any (·.isEmpty) then
        .error s!"the upload base '{base}' does not name a bucket \
          (the rclone engine needs https://endpoint/bucket)"
      else
        .ok (s!"{scheme}://{host}", "/".intercalate parts)
    | [] => .error s!"the upload base '{base}' is not a URL"
  | _ => .error s!"the upload base '{base}' is not a URL"

/--
The rclone S3 backend configuration, passed through the child environment so
no credential reaches a command line. `RCLONE_S3_SESSION_TOKEN` is set for a
temporary credential and cleared otherwise, so a stale token in the caller's
environment is not inherited. Region `auto` matches the curl engine's SigV4
region. rclone refuses to run without a provider, so `provider` must carry
one; `putStagedViaRclone` keeps the caller's `RCLONE_S3_PROVIDER` and
defaults to the generic `Other`. Every other `RCLONE_S3_*` option inherits
from the caller, so an operator can tune transfers without a tool change.
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
