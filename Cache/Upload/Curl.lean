/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Requests
public import Cache.Marker

/-!
# The curl upload tool

The built-in transfer tool: parallel curl PUTs to the resolved location
(`Location`). Each backend module
(`Cache/Upload/Azure.lean`, `Cache/Upload/S3.lean`) calls the tool's entry
point, `putStagedViaCurl`, with its own per-request signing arguments.
-/

public section

namespace Cache.Requests

open System (FilePath)

/--
The per-request curl arguments for one upload PUT: the backend's signing
arguments plus the non-overwrite guard. A non-overwrite put adds
`If-None-Match: *`, which every backend answers with 409/412 for an object
that already exists (`classifyUpload` excuses those).

Every backend passes its secrets in the argument list, so callers should print curl
failures without the argument list (`showArgsOnError := false`).
-/
def uploadPutArgs (signArgs : Array String) (overwrite : Bool) : Array String :=
  if overwrite then signArgs else signArgs ++ #["-H", "If-None-Match: *"]

/-- Build the upload config. Response bodies go to `bodySink`, leaving stdout
for transfer reports. The sink must support truncation for retries (curl issue #17371). -/
def mkPutConfigContent (dest : Location) (files : Array FilePath) (bodySink : FilePath) :
    String :=
  let l := files.toList.map fun file : FilePath =>
    s!"-T {file.toString}\nurl = {dest.fileURL file.fileName.get!}\n\
      -o {bodySink.toString}"
  "\n".intercalate l

/-- Upload files with curl and exit with code 1 if any transfer fails.
Parallel uploads use the `MATHLIB_CACHE_PARALLEL_MAX` limit. -/
def putFilesViaCurl
    (dest : Location) (files : Array FilePath) (tempConfigFilePath : FilePath)
    (overwrite : Bool) (signArgs : Array String) : IO Unit := do
  -- TODO: reimplement using HEAD requests?
  let size := files.size
  if size > 0 then
    -- A shared regular file supports truncation when curl retries.
    let bodySink := tempConfigFilePath.withExtension "body"
    IO.FS.writeFile tempConfigFilePath (mkPutConfigContent dest files bodySink)
    IO.println
      s!"Attempting to upload {size} file(s) under {dest.root}/{dest.filesDir} \
        (location: {dest.label})"
    -- A retry after a PUT that landed is safe: the server answers a
    -- non-overwrite retry with 409/412, which `classifyUpload` excuses, and
    -- an overwrite retry re-sends the same bytes.
    let args := uploadPutArgs signArgs overwrite ++
      #["-X", "PUT", "--parallel", "--silent", "--show-error"] ++
      (← curlParallelMaxArgs) ++
      curlRetryArgs (supportLegacyCurl := false) ++
      -- `%{json}` prints a JSON report for each finished transfer. The
      -- leading newline keeps each report on its own line even if something
      -- else reaches stdout ahead of it.
      #["--write-out", "\n%{json}\n", "--config", tempConfigFilePath.toString]
    let (s, _) ← monitorCurl args size "Uploaded" "speed_upload"
      (classifyUpload · · !overwrite) (removeOnError := false) (decompConfig := none)
    IO.FS.removeFile tempConfigFilePath
    if ← bodySink.pathExists then IO.FS.removeFile bodySink
    -- Surface genuine upload failures. `monitorCurl` excuses already-present
    -- blobs (409/412 on a non-overwrite put), so a re-upload of files the
    -- server already has does not trip this.
    if s.failed > 0 then
      let unreported := files.filter fun file =>
        !s.reported.contains (dest.fileURL file.fileName.get!)
      unless unreported.isEmpty do
        IO.eprintln s!"files without a curl report: \
          {" ".intercalate (unreported.toList.map (·.fileName.get!))}"
      IO.eprintln s!"Uploading {s.failed} file(s) failed"
      IO.Process.exit 1
  else IO.println "No files to upload"

/-- Upload the named staged files, then the location's marker if present.
`getSignArgs` supplies signing arguments for each upload.
File failures exit with code 1; marker failures only warn. -/
def putStagedViaCurl (dest : Location) (getSignArgs : IO (Array String))
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool) : IO Unit := do
  discard <| IO.validateCurl (upload := true)
  let files := fileNames.map fun (f : String) => srcDir / f
  putFilesViaCurl dest files (IO.curlConfigIn srcDir) overwrite (← getSignArgs)
  uploadMarker dest fun marker file => do
    -- A marker may be overwritten freely, so its PUT carries no
    -- non-overwrite guard.
    let args := uploadPutArgs (← getSignArgs) (overwrite := true) ++
      #["-X", "PUT", "-T", file.toString, marker.url]
    -- The argument list carries the credential; keep it out of the failure message.
    discard <| IO.runCurl args (showArgsOnError := false) (upload := true)

end Cache.Requests
