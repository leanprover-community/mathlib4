/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/

import Cache.Upload

/-!
# The rclone upload engine

An opt-in transfer engine: a system [rclone](https://rclone.org) against the
resolved destination (`StagedUploadDest`), with the S3 credentials passed
through its environment. `putStagedViaRclone` is the engine's entry point;
`Cache/Uploader.lean` dispatches to it.
-/

namespace Cache.Requests

open System (FilePath)

/-- Whether a working rclone is available on PATH. -/
def rcloneAvailable : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "rclone", args := #["version"] }
    return out.exitCode == 0
  catch _ =>
    return false

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
the curl engine's marker put, so the copy omits `--ignore-existing`.
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
and `fileNames` lists the ones to upload; the list is passed as a
`--files-from` file, so only the named files leave the machine. Files first;
then the per-SHA marker, mirroring the curl engine. A files failure exits 1; a
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
