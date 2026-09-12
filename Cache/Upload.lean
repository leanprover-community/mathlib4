/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# Cache uploads

Everything that moves staged bytes to a cache destination lives here:

* the upload credentials (`UploadAuth`) and their resolution from the
  environment;
* the one destination resolution every upload consumes
  (`StagedUploadDest`, `stagedUploadDest`);
* the transfer engines: the built-in curl engine (`putFilesAbsolute`), a
  system rclone (`putStagedViaRclone`), and the external uploader hook
  (`putStagedViaHook`);
* the per-SHA marker upload (`uploadMarker`).

The read side (`Cache/Requests.lean`) shares the path contract through
`filePathPrefix` and `markerDirPath` (`Cache/Infra.lean`), so no upload
engine can drift from the URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- Authentication method used for cache upload operations. -/
inductive UploadAuth where
  | azureSas (token : String)
  | azureBearer (token : String)
  /-- S3-compatible credentials for a direct bucket write, signed per request
  with SigV4 by curl. `sessionToken?` carries the session token of a temporary
  credential — what the cache broker mints for CI against a GitHub OIDC
  token — and is absent for a static keypair. -/
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
3. `MATHLIB_CACHE_SAS`.

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
    | none, some token => .ok (.azureSas token)
    | none, none => .error
        "environment variable MATHLIB_CACHE_S3_ACCESS_KEY_ID/MATHLIB_CACHE_S3_SECRET_ACCESS_KEY, \
        MATHLIB_CACHE_AZURE_BEARER_TOKEN or MATHLIB_CACHE_SAS must be set to upload caches"

/--
Capability tokens `cache capabilities` prints, one per line. CI probes them to
decide which upload flows this tool supports, so the list is declared beside
the code that implements the capabilities and moves with it:

* `s3-put`: `put` signs uploads with the S3 credentials
  (`uploadAuthFrom`'s first branch).
* `upload-hook`: `put` delegates transfers to `MATHLIB_CACHE_UPLOAD_HOOK`.
* `rclone-put`: `put` can drive a system rclone for S3 uploads
  (`MATHLIB_CACHE_UPLOADER`).
-/
def capabilities : List String := ["s3-put", "upload-hook", "rclone-put"]

/-- Retrieves upload credentials from the environment via `uploadAuthFrom`. -/
def getUploadAuth : IO UploadAuth := do
  let auth := uploadAuthFrom
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_ACCESS_KEY_ID")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SECRET_ACCESS_KEY")
    (← getEnvNonEmpty "MATHLIB_CACHE_S3_SESSION_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_AZURE_BEARER_TOKEN")
    (← getEnvNonEmpty "MATHLIB_CACHE_SAS")
  match auth with
  | .ok auth => return auth
  | .error e => throw <| IO.userError e


/-- The misconfiguration the upload-destination resolver reports for a put
base without a container. -/
def uploadBaseNoContainerError : String :=
  "MATHLIB_CACHE_PUT_BASE_URL is set, which rebases a container write; \
  pass --container=NAME to name the container."

/-- The warning the upload-destination resolver prints when an upload names
no container and no endpoint override, and falls back to `legacy`. -/
def warnUploadLegacyFallback : IO Unit :=
  IO.eprintln <|
    "Warning: cache upload without --container=NAME; defaulting to the\n" ++
    "         `legacy` (bare `mathlib4`) container. Pass --container=NAME\n" ++
    "         explicitly to choose a trust-level container."

/--
The resolved destination of a staged (`put`) upload, in the form the external
uploader hook consumes: `base` is the upload base the operator configured, and
the prefixes are relative to it, with no trailing slash. Every staged file
lands under `filesPrefix` with its base name kept; the per-SHA marker lands
under `markerPrefix` with the SHA as its name.
-/
structure StagedUploadDest where
  base : String
  filesPrefix : String
  markerPrefix : String
  deriving Repr, BEq

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

The prefixes build on `filePathPrefix` and `markerDirPath`, the same policies
the reads use, so no upload path can drift from the path contract.
-/
def stagedUploadDestFrom (putUrl? putBase? : Option String)
    (container? : Option Container) (repo : String) (scope? : Option String) :
    Except String StagedUploadDest :=
  let filesRel := fun (c? : Option Container) =>
    let pre := filePathPrefix c? repo scope?
    -- `filePathPrefix` is empty or `/`-terminated; the hook contract carries
    -- no trailing slash.
    if pre.isEmpty then "f" else s!"f/{(pre.dropEnd 1).copy}"
  let markerRel := markerDirPath repo
  let under := fun (c : Container) (rel : String) => s!"{c.pathSegment}/{rel}"
  if let some url := putUrl? then
    -- A user-supplied URL carries no container policy; the prefix follows the
    -- repo alone, flat for `MATHLIBREPO` and repo-namespaced otherwise.
    .ok { base := url, filesPrefix := filesRel none, markerPrefix := markerRel }
  else
    match normalizeBaseURL putBase?, container? with
    | some base, some c =>
      .ok { base, filesPrefix := under c (filesRel (some c)),
            markerPrefix := under c markerRel }
    | some _, none => .error uploadBaseNoContainerError
    | none, some c =>
      .ok { base := azureAccountURL, filesPrefix := under c (filesRel (some c)),
            markerPrefix := under c markerRel }
    | none, none =>
      .ok { base := azureAccountURL,
            filesPrefix := under .legacy (filesRel (some .legacy)),
            markerPrefix := under .legacy markerRel }

/--
`stagedUploadDestFrom`, resolved from the environment. The one destination
resolution every upload consumes: the curl artifact puts, the marker put, and
the hook all address `{base}/{prefix}/{name}`.
-/
def stagedUploadDest (container? : Option Container) (repo : String) :
    IO StagedUploadDest := do
  let putUrl? ← IO.getEnv "MATHLIB_CACHE_PUT_URL"
  let putBase? ← IO.getEnv "MATHLIB_CACHE_PUT_BASE_URL"
  if putUrl?.isNone && (normalizeBaseURL putBase?).isNone && container?.isNone then
    warnUploadLegacyFallback
  match stagedUploadDestFrom putUrl? putBase? container? repo (← getRepoScope) with
  | .error e => throw <| IO.userError e
  | .ok dest => return dest

/--
Run the external upload hook once: `hook <localPath> <relativeDest>
<absoluteDest>`. The hook copies the named file — or the `*.ltar` files of the
named directory — into the destination prefix, preserving base names, with
whatever transport and credentials it owns; the tool passes it no credential.
`relativeDest` is relative to the configured upload base and `absoluteDest` is
`{base}/{relativeDest}`; a hook uses whichever fits its remote naming. The
hook's output passes through to the user; the returned exit code is the
hook's.
-/
def runUploadHook (hook : String) (localPath : FilePath) (dest : StagedUploadDest)
    (rel : String) : IO UInt32 := do
  let child ← IO.Process.spawn
    { cmd := hook, args := #[localPath.toString, rel, s!"{dest.base}/{rel}"] }
  child.wait

/--
`put` through the external uploader hook (`MATHLIB_CACHE_UPLOAD_HOOK`): the
tool resolves the destination contract and the hook does the transfers. Files
first; then, mirroring the curl path, the per-SHA marker when a scope and a
container are given — written as a file named after the SHA, so the hook's
basename-preserving copy lands it at `{markerPrefix}/{sha}`. A files failure
exits 1; a marker failure only warns, as on the curl path.

One contract difference from the curl path: curl uploads send
`If-None-Match: *` and never replace an existing object, while overwrite
behavior here is the hook's own. Artifact names are content hashes, so an
honest re-put writes identical bytes; a hook that can decline existing
objects (rclone `--ignore-existing`, say) restores the full guarantee.
-/
def putStagedViaHook (hook : String) (dest : StagedUploadDest)
    (markerSha? : Option String) (stagingDir : FilePath) : IO Unit := do
  let count := (← IO.getFilesWithExtension stagingDir "ltar").size
  IO.println s!"Uploading {count} staged file(s) via {hook} to \
    {dest.base}/{dest.filesPrefix}"
  let code ← runUploadHook hook stagingDir dest dest.filesPrefix
  if code != 0 then
    IO.eprintln s!"upload hook failed with exit code {code}"
    IO.Process.exit 1
  if let some sha := markerSha? then
      let dir ← IO.FS.createTempDir
      try
        let markerFile := dir / sha
        IO.FS.writeFile markerFile s!"{sha}\n"
        let code ← runUploadHook hook markerFile dest dest.markerPrefix
        if code != 0 then
          IO.eprintln s!"warning: marker upload via hook failed (exit code {code})"
      finally
        IO.FS.removeDirAll dir

def azureBearerApiVersionHeader : String := "x-ms-version: 2026-02-06"

def getAzureDateHeader : IO String := do
  let out ← IO.Process.output
    { cmd := "date", args := #["-u", "+%a, %d %b %Y %H:%M:%S GMT"] }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"failed to produce x-ms-date header (exit code {out.exitCode})"
  return s!"x-ms-date: {out.stdout.trimAscii.copy}"

/--
Query string an upload appends to each destination URL: `?{token}` for SAS
auth, which signs through the URL, and empty for the header-based mechanisms.
-/
def UploadAuth.sasQuery : UploadAuth → String
  | .azureSas token => s!"?{token}"
  | _ => ""

/--
The authentication and header curl arguments for an upload with `auth`, shared
by the artifact, commit, and marker PUT paths. A non-overwrite put adds
`If-None-Match: *`, which Azure and S3-compatible backends answer with 409/412
for a blob that already exists (`classifyUpload` excuses those).

* Azure needs the `x-ms-blob-type` header; the bearer form adds the api-version
  and date headers and the OAuth token.
* SAS signs through the URL query (`UploadAuth.sasQuery`), so it contributes
  only the Azure headers here.
* S3 signs each request with SigV4 (`--aws-sigv4`; region `auto` fits R2). The
  explicit `x-amz-content-sha256: UNSIGNED-PAYLOAD` header is what lets curl
  sign a `-T` file upload (supported from curl 7.87); this path runs in CI,
  whose runners ship newer curls. A temporary credential also sends its session
  token, which SigV4 covers as an `x-amz-*` header.

The token and keypair travel in the argument list, as the bearer token always
has; callers therefore print curl failures without their argument lists
(`showArgsOnError := false`).
-/
def uploadAuthArgs (auth : UploadAuth) (overwrite : Bool) : IO (Array String) := do
  let ifNoneMatch : Array String := if overwrite then #[] else #["-H", "If-None-Match: *"]
  match auth with
  | .azureSas _ =>
    return #["-H", "x-ms-blob-type: BlockBlob"] ++ ifNoneMatch
  | .azureBearer token =>
    return #["-H", "x-ms-blob-type: BlockBlob"] ++ ifNoneMatch ++
      #["-H", azureBearerApiVersionHeader, "-H", ← getAzureDateHeader,
        "--oauth2-bearer", token]
  | .s3 keyId secret sessionToken? =>
    let sessionArgs : Array String := match sessionToken? with
      | some token => #["-H", s!"x-amz-security-token: {token}"]
      | none => #[]
    return #["--aws-sigv4", "aws:amz:auto:s3", "--user", s!"{keyId}:{secret}",
      "-H", "x-amz-content-sha256: UNSIGNED-PAYLOAD"] ++ sessionArgs ++ ifNoneMatch

/-- Formats the config file for `curl`, containing the list of files to be
uploaded: each staged file lands at `{base}/{filesPrefix}/{fileName}`, with
the destination resolved once by `stagedUploadDest`. The response body goes
to the null device: stdout must carry only the per-transfer JSON reports that
`monitorCurl` parses. -/
def mkPutConfigContent (dest : StagedUploadDest) (files : Array FilePath)
    (auth : UploadAuth) : String :=
  let token := auth.sasQuery
  let l := files.toList.map fun file : FilePath =>
    s!"-T {file.toString}\nurl = {dest.base}/{dest.filesPrefix}/{file.fileName.get!}{token}\n\
      -o {IO.nullDevice}"
  "\n".intercalate l

/-- Calls `curl` to send a set of files to the already-resolved destination
(see `stagedUploadDest`). `target` names the destination in the progress
message: the container name, or a note that an endpoint override applies. -/
def putFilesAbsolute
  (dest : StagedUploadDest) (target : String)
  (files : Array FilePath) (tempConfigFilePath : FilePath)
  (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let size := files.size
  if size > 0 then
    IO.FS.writeFile tempConfigFilePath (mkPutConfigContent dest files auth)
    IO.println s!"Attempting to upload {size} file(s) under {dest.filesPrefix} (container: {target})"
    let args ← uploadAuthArgs auth overwrite
    -- A retry after a PUT that landed is safe: a non-overwrite put answers
    -- it with 409/412, which `classifyUpload` excuses, and an overwrite
    -- put re-sends the same bytes.
    let args := args ++ #["-X", "PUT", "--parallel"] ++
      curlRetryArgs (supportLegacyCurl := false) ++
      -- `%{json}` prints a JSON report for each finished transfer. The
      -- leading newline keeps each report on its own line even if something
      -- else reaches stdout ahead of it.
      #["--write-out", "\n%{json}\n", "--config", tempConfigFilePath.toString]
    let (s, _) ← monitorCurl args size "Uploaded" "speed_upload"
      (classifyUpload · · !overwrite) (removeOnError := false) (decompConfig := none)
    IO.FS.removeFile tempConfigFilePath
    -- Surface genuine upload failures. Already-present blobs (409/412 on a
    -- non-overwrite put) are excused in `monitorCurl`, so this won't trip on a
    -- re-upload of files the server already has.
    if s.failed > 0 then
      IO.eprintln s!"Uploading {s.failed} file(s) failed"
      IO.Process.exit 1
  else IO.println "No files to upload"

/--
Upload a tiny marker blob to `{markerPrefix}/{sha}` of the already-resolved
destination (see `stagedUploadDest`), so the marker lands where the artifacts
just went. The blob content is the SHA itself, as a debugging aid; existence
is the signal.

Called from `cache put` after the `.ltar` artifact uploads complete. A marker
overwrites freely (its content is its own name), so a re-upload of an
already-marked commit does not fail here. If this PUT fails the artifacts are
already uploaded — the only loss is that `cache query` will not find this
commit — so failures here are logged but not fatal.

A marker speaks only for its own destination: it asserts that the writing
`put` completed there. When several destinations receive uploads
independently, one destination's markers do not assert that it holds a
commit's full transitive closure; the infrastructure documentation governs
when a destination's markers may be trusted for completeness.
-/
def uploadMarker (dest : StagedUploadDest) (sha : String) (auth : UploadAuth) :
    IO Unit := do
  let url := s!"{dest.base}/{dest.markerPrefix}/{sha}"
  let path := IO.CACHEDIR / s!"marker-{sha}"
  IO.FS.createDirAll IO.CACHEDIR
  IO.FS.writeFile path s!"{sha}\n"
  try
    let args := (← uploadAuthArgs auth (overwrite := true)) ++
      #["-X", "PUT", "-T", path.toString, s!"{url}{auth.sasQuery}"]
    -- The argument list carries the credential; keep it out of the failure message.
    discard <| IO.runCurl args (showArgsOnError := false)
  catch e =>
    IO.eprintln s!"warning: marker upload to {url} failed: {e}"
  IO.FS.removeFile path

/--
The built-in transfer engine `put` uses when no external uploader hook is
configured: the curl engine, or a system rclone.
-/
inductive UploadEngine where
  | curl
  | rclone
  deriving DecidableEq, Repr, BEq

/-- Whether the credentials are the S3 pair (the mechanism rclone signs with). -/
def UploadAuth.isS3 : UploadAuth → Bool
  | .s3 .. => true
  | _ => false

/--
Resolve the transfer engine from `MATHLIB_CACHE_UPLOADER` (`uploader?`):

* unset or `curl`: the built-in curl engine.
* `rclone`: a system rclone, required — a missing binary or non-S3
  credentials error rather than silently changing engines.
* `auto`: rclone when the binary answers and the credentials are the S3
  pair; the curl engine otherwise. rclone signs S3 requests only, so the
  Azure mechanisms always take the curl engine.

Pure so the policy is testable; `resolveUploadEngine` wires the environment
and the availability probe in.
-/
def uploadEngineFrom (uploader? : Option String) (authIsS3 rcloneAvailable : Bool) :
    Except String UploadEngine :=
  match uploader? with
  | none => .ok .curl
  | some "curl" => .ok .curl
  | some "rclone" =>
    if !authIsS3 then
      .error "MATHLIB_CACHE_UPLOADER=rclone signs uploads with the S3 credential pair, \
        and the environment provides a different upload mechanism"
    else if !rcloneAvailable then
      .error "MATHLIB_CACHE_UPLOADER=rclone, but rclone did not answer on PATH"
    else .ok .rclone
  | some "auto" => .ok (if authIsS3 && rcloneAvailable then .rclone else .curl)
  | some other =>
    .error s!"unknown MATHLIB_CACHE_UPLOADER value '{other}' (known: curl, rclone, auto)"

/-- Whether a working rclone answers on PATH. -/
def rcloneAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "rclone", args := #["version"] }
    return out.exitCode == 0
  catch _ =>
    return false

/--
`uploadEngineFrom` on the environment. The availability probe runs only for
the `MATHLIB_CACHE_UPLOADER` values whose outcome depends on it.
-/
def resolveUploadEngine (auth : UploadAuth) : IO UploadEngine := do
  let uploader? ← getEnvNonEmpty "MATHLIB_CACHE_UPLOADER"
  let available ←
    if uploader? == some "rclone" || uploader? == some "auto" then rcloneAvailable
    else pure false
  match uploadEngineFrom uploader? auth.isS3 available with
  | .ok engine => return engine
  | .error e => throw <| IO.userError e

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

/-- The rclone flags every `put` transfer carries. `--s3-no-check-bucket`
skips the bucket-creation probe a scoped credential cannot pass. -/
def rcloneCommonFlags : Array String := #["--s3-no-check-bucket", "--retries", "5"]

/--
The rclone invocation for the staged `.ltar` files: a directory copy into the
files prefix. `--ignore-existing` declines objects the destination already
holds, matching the curl engine's `If-None-Match: *`; artifact names are
content hashes, so a skipped re-put loses nothing.
-/
def rcloneFilesArgs (bucketPath : String) (dest : StagedUploadDest)
    (stagingDir : FilePath) : Array String :=
  #["copy", stagingDir.toString, s!":s3:{bucketPath}/{dest.filesPrefix}",
    "--include", "*.ltar", "--ignore-existing", "--transfers", "16"] ++ rcloneCommonFlags

/--
The rclone invocation for the per-SHA marker: a single-file copy to the
marker path. A marker overwrites freely (its content is its own name), like
the curl engine's marker put, so no `--ignore-existing` here.
-/
def rcloneMarkerArgs (bucketPath : String) (dest : StagedUploadDest)
    (markerFile : FilePath) (sha : String) : Array String :=
  #["copyto", markerFile.toString, s!":s3:{bucketPath}/{dest.markerPrefix}/{sha}"] ++
    rcloneCommonFlags

/--
The rclone S3 backend configuration, passed through the child environment so
no credential reaches a command line. `RCLONE_S3_SESSION_TOKEN` is set for a
temporary credential and cleared otherwise, so a stale token in the caller's
environment cannot ride along. Region `auto` matches the curl engine's SigV4
region. rclone refuses to run without a provider, so `provider` must carry
one; `putStagedViaRclone` keeps the caller's `RCLONE_S3_PROVIDER` and
defaults to the generic `Other`. Every other `RCLONE_S3_*` option inherits
from the caller, so an operator can tune transfers without a tool change.
-/
def rcloneEnv (keyId secret : String) (sessionToken? : Option String)
    (endpoint provider : String) : Array (String × Option String) :=
  #[("RCLONE_S3_ENV_AUTH", some "false"),
    ("RCLONE_S3_ACCESS_KEY_ID", some keyId),
    ("RCLONE_S3_SECRET_ACCESS_KEY", some secret),
    ("RCLONE_S3_SESSION_TOKEN", sessionToken?),
    ("RCLONE_S3_ENDPOINT", some endpoint),
    ("RCLONE_S3_PROVIDER", some provider),
    ("RCLONE_S3_REGION", some "auto")]

/--
`put` through a system rclone: the tool resolves the destination and hands
rclone the S3 credentials through its environment. Files first; then the
per-SHA marker, mirroring the curl engine. A files failure exits 1; a marker
failure only warns. The `rclone` parameter names the binary and exists for
the tests; production callers use the default.
-/
def putStagedViaRclone (dest : StagedUploadDest) (keyId secret : String)
    (sessionToken? : Option String) (markerSha? : Option String)
    (stagingDir : FilePath) (rclone : String := "rclone") : IO Unit := do
  let (endpoint, bucketPath) ← match s3EndpointSplit dest.base with
    | .ok parts => pure parts
    | .error e => throw <| IO.userError e
  let provider := (← getEnvNonEmpty "RCLONE_S3_PROVIDER").getD "Other"
  let env := rcloneEnv keyId secret sessionToken? endpoint provider
  let run := fun (args : Array String) => do
    let child ← IO.Process.spawn { cmd := rclone, args, env }
    child.wait
  let count := (← IO.getFilesWithExtension stagingDir "ltar").size
  IO.println s!"Uploading {count} staged file(s) via rclone to \
    {dest.base}/{dest.filesPrefix}"
  let code ← run (rcloneFilesArgs bucketPath dest stagingDir)
  if code != 0 then
    IO.eprintln s!"rclone upload failed with exit code {code}"
    IO.Process.exit 1
  if let some sha := markerSha? then
    let dir ← IO.FS.createTempDir
    try
      let markerFile := dir / sha
      IO.FS.writeFile markerFile s!"{sha}\n"
      let code ← run (rcloneMarkerArgs bucketPath dest markerFile sha)
      if code != 0 then
        IO.eprintln s!"warning: marker upload via rclone failed (exit code {code})"
    finally
      IO.FS.removeDirAll dir

end Cache.Requests
