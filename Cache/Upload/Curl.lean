/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload.Defs

/-!
# The curl upload engine

The built-in transfer engine: parallel curl PUTs against the resolved
destination (`StagedUploadDest`), authenticated per request from the
`UploadAuth` mechanism (`uploadAuthArgs`). `putStagedViaCurl` is the engine's
entry point; `Cache/Upload.lean` dispatches to it.
-/

namespace Cache.Requests

open System (FilePath)

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

Every mechanism's secrets are passed in the argument list; callers therefore
print curl failures without their argument lists (`showArgsOnError := false`).
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
uploaded: each staged file is uploaded to its `StagedUploadDest.fileURL`, with
the destination resolved once by `stagedUploadDest`. The response body goes
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
The staged put on the curl engine: the `.ltar` files named by `fileNames`
under `srcDir`, then the per-SHA marker when `markerSha?` names one. The curl
config file is written to `srcDir` for the duration of the transfer. A files
failure exits 1; a marker failure only warns (see `uploadMarkerWith`).
-/
def putStagedViaCurl (dest : StagedUploadDest) (srcDir : FilePath)
    (fileNames : Array String) (overwrite : Bool) (auth : UploadAuth)
    (markerSha? : Option String) : IO Unit := do
  let files := fileNames.map fun (f : String) => srcDir / f
  putFilesViaCurl dest files (srcDir / "curl.config") overwrite auth
  if let some sha := markerSha? then
    uploadMarkerWith dest sha fun file => do
      let args := (← uploadAuthArgs auth (overwrite := true)) ++
        #["-X", "PUT", "-T", file.toString, dest.markerURL sha]
      -- The argument list carries the credential; keep it out of the failure message.
      discard <| IO.runCurl args (showArgsOnError := false)

end Cache.Requests
