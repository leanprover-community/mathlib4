/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Marker

/-!
# Cache uploads

This module holds everything that moves staged bytes to a cache destination:

* the upload credentials (`UploadAuth`) and their resolution from the
  environment;
* the one destination resolution every upload consumes
  (`StagedUploadDest`, `stagedUploadDest`);
* the transfer engines — the built-in curl engine (`putStagedViaCurl`) and a
  system rclone (`putStagedViaRclone`) — and the policy that picks one
  (`UploadEngine`, `resolveUploadEngine`);
* the per-SHA marker upload both engines share (`uploadMarkerWith`).

The read side (`Cache/Requests.lean`) shares the path contract through
`fileDirPath` and `markerDirPath` (`Cache/Infra.lean`), so every upload
engine addresses the URLs the readers probe.
-/

namespace Cache.Requests

open System (FilePath)

/-- Authentication method used for cache upload operations. -/
inductive UploadAuth where
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
slash. Every staged file lands under `filesPrefix` with its base name kept;
the per-SHA marker lands under `markerPrefix` with the SHA as its name
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

/--
Write the marker file for `sha` and hand it to `transfer`, which moves it to
`{markerPrefix}/{sha}` of the resolved destination — the marker mechanics both
engines share. The blob content is the SHA itself, as a debugging aid;
existence is the signal. A marker overwrites freely (its content is its own
name), so a re-upload of an already-marked commit does not fail here.

Runs after the `.ltar` artifact uploads complete, and a `transfer` failure
warns instead of throwing: the artifacts are already uploaded — the only loss
is that `cache query` will not find this commit.

A marker applies only to its own destination: it records that the writing
`put` completed there. When several destinations receive uploads
independently, one destination's marker does not say that the destination
holds a commit's full transitive closure; the infrastructure documentation
governs when a destination's markers may be trusted for completeness.
-/
def uploadMarkerWith (dest : StagedUploadDest) (sha : String)
    (transfer : FilePath → IO Unit) : IO Unit := do
  let dir ← IO.FS.createTempDir
  try
    let file := dir / sha
    IO.FS.writeFile file s!"{sha}\n"
    transfer file
  catch e =>
    IO.eprintln s!"warning: marker upload to {dest.markerURL sha} failed: {e}"
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
The authentication and header curl arguments for an upload with `auth`, shared
by the artifact and marker PUT paths. A non-overwrite put adds
`If-None-Match: *`, which Azure and S3-compatible backends answer with 409/412
for a blob that already exists (`classifyUpload` excuses those).

* Azure needs the `x-ms-blob-type` header, the api-version and date headers,
  and the OAuth token.
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
uploaded: each staged file lands at its `StagedUploadDest.fileURL`, with the
destination resolved once by `stagedUploadDest`. The response body goes
to the null device: stdout must carry only the per-transfer JSON reports that
`monitorCurl` parses. -/
def mkPutConfigContent (dest : StagedUploadDest) (files : Array FilePath) : String :=
  let l := files.toList.map fun file : FilePath =>
    s!"-T {file.toString}\nurl = {dest.fileURL file.fileName.get!}\n\
      -o {IO.nullDevice}"
  "\n".intercalate l

/-- Calls `curl` to send a set of files to the already-resolved destination
(see `stagedUploadDest`). Exits with code 1 when any file fails to upload. -/
def putFilesViaCurl
    (dest : StagedUploadDest) (files : Array FilePath) (tempConfigFilePath : FilePath)
    (overwrite : Bool) (auth : UploadAuth) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let size := files.size
  if size > 0 then
    IO.FS.writeFile tempConfigFilePath (mkPutConfigContent dest files)
    IO.println
      s!"Attempting to upload {size} file(s) under {dest.filesPrefix} (container: {dest.label})"
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
The staged put on the built-in curl engine: the artifact files, then the
per-SHA marker when `markerSha?` names one. A files failure exits 1; a marker
failure only warns (see `uploadMarkerWith`).
-/
def putStagedViaCurl (dest : StagedUploadDest) (files : Array FilePath)
    (tempConfigFilePath : FilePath) (overwrite : Bool) (auth : UploadAuth)
    (markerSha? : Option String) : IO Unit := do
  putFilesViaCurl dest files tempConfigFilePath overwrite auth
  if let some sha := markerSha? then
    uploadMarkerWith dest sha fun file => do
      let args := (← uploadAuthArgs auth (overwrite := true)) ++
        #["-X", "PUT", "-T", file.toString, dest.markerURL sha]
      -- The argument list carries the credential; keep it out of the failure message.
      discard <| IO.runCurl args (showArgsOnError := false)

/--
The transfer engine `put` uses, resolved together with the credentials it
signs with: the built-in curl engine works with every credential mechanism,
while rclone signs S3 requests only, so its constructor carries the S3
credentials — an rclone engine holding a non-S3 credential is unrepresentable.
-/
inductive UploadEngine where
  | curl
  | rclone (keyId secret : String) (sessionToken? : Option String)
  deriving DecidableEq, Repr, BEq

/--
Resolve the transfer engine from the `--uploader=` option (`uploader?`):

* unset or `curl`: the built-in curl engine.
* `rclone`: a system rclone, required — a missing binary or non-S3
  credentials error rather than silently changing engines. rclone signs S3
  requests only, so the Azure mechanisms always take the curl engine.

Pure so the policy is testable; `resolveUploadEngine` wires the availability
probe in.
-/
def uploadEngineFrom (uploader? : Option String) (auth : UploadAuth)
    (rcloneAvailable : Bool) : Except String UploadEngine :=
  let rclone? : Option UploadEngine := match auth with
    | .s3 keyId secret sessionToken? => some (.rclone keyId secret sessionToken?)
    | .azureBearer _ => none
  match uploader? with
  | none | some "curl" => .ok .curl
  | some "rclone" =>
    match rclone? with
    | none => .error "--uploader=rclone signs uploads with the S3 credential pair, \
        and the environment provides a different upload mechanism"
    | some engine =>
      if rcloneAvailable then .ok engine
      else .error "--uploader=rclone, but no working rclone was found on PATH"
  | some other =>
    .error s!"unknown --uploader value '{other}' (known: curl, rclone)"

/-- Whether a working rclone is available on PATH. -/
def rcloneAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "rclone", args := #["version"] }
    return out.exitCode == 0
  catch _ =>
    return false

/--
`uploadEngineFrom` with the availability probe wired in. The probe runs only
when `--uploader=rclone` asks for the binary.
-/
def resolveUploadEngine (uploader? : Option String) (auth : UploadAuth) :
    IO UploadEngine := do
  let available ← if uploader? == some "rclone" then rcloneAvailable else pure false
  IO.ofExcept <| uploadEngineFrom uploader? auth available

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
The rclone invocation for the `.ltar` files: a copy from `srcDir` into the
files prefix, restricted to the `--files-from` list, so only the files the
caller names leave the machine. A non-overwrite put passes
`--ignore-existing`, which skips objects the destination already holds,
matching the curl engine's `If-None-Match: *`; artifact names are content
hashes, so a skipped re-put loses nothing.
-/
def rcloneFilesArgs (bucketPath : String) (dest : StagedUploadDest)
    (srcDir filesFrom : FilePath) (overwrite : Bool) : Array String :=
  #["copy", srcDir.toString, s!":s3:{bucketPath}/{dest.filesPrefix}",
    "--files-from", filesFrom.toString, "--transfers", "16"] ++
    (if overwrite then #[] else #["--ignore-existing"]) ++ rcloneCommonFlags

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
environment is not inherited. Region `auto` matches the curl engine's SigV4
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
The staged put on a system rclone: the tool resolves the destination and hands
rclone the S3 credentials through its environment. `srcDir` holds the files
and `fileNames` lists the ones to upload; the list travels as a `--files-from`
file, so only the named files leave the machine — `put`'s build-scoped list
and `put-staged`'s staging directory both take this engine. Files first; then
the per-SHA marker, mirroring the curl engine. A files failure exits 1; a
marker failure only warns (see `uploadMarkerWith`). The `rclone` parameter
names the binary and exists for the tests; production callers use the default.
-/
def putStagedViaRclone (dest : StagedUploadDest) (keyId secret : String)
    (sessionToken? : Option String) (markerSha? : Option String)
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool)
    (rclone : String := "rclone") : IO Unit := do
  let (endpoint, bucketPath) ← IO.ofExcept (s3EndpointSplit dest.base)
  let provider := (← getEnvNonEmpty "RCLONE_S3_PROVIDER").getD "Other"
  let env := rcloneEnv keyId secret sessionToken? endpoint provider
  let run (args : Array String) : IO UInt32 := do
    let child ← IO.Process.spawn { cmd := rclone, args, env }
    child.wait
  if fileNames.isEmpty then
    IO.println "No files to upload"
  else
    IO.println s!"Uploading {fileNames.size} file(s) via rclone to \
      {dest.base}/{dest.filesPrefix}"
    let dir ← IO.FS.createTempDir
    let code ← try
      let filesFrom := dir / "files-from.txt"
      IO.FS.writeFile filesFrom ("\n".intercalate fileNames.toList ++ "\n")
      run (rcloneFilesArgs bucketPath dest srcDir filesFrom overwrite)
    finally
      IO.FS.removeDirAll dir
    if code != 0 then
      IO.eprintln s!"rclone upload failed with exit code {code}"
      IO.Process.exit 1
  if let some sha := markerSha? then
    uploadMarkerWith dest sha fun file => do
      let code ← run (rcloneMarkerArgs bucketPath dest file sha)
      unless code == 0 do
        throw <| IO.userError s!"rclone exited with code {code}"

end Cache.Requests
