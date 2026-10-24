/-
Copyright (c) 2026 Marcelo Lynch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcelo Lynch
-/
module

public import Cache.Requests
public import Cache.Marker

/-!
# The rclone upload tool

Upload cache files with a system [rclone](https://rclone.org).
The S3 backend supplies credentials and endpoint settings through the child environment.
-/

public section

namespace Cache.Requests

open System (FilePath)

/-- Split an S3 URL into its endpoint origin and bucket path. The path keeps
any prefix after the bucket, including a container segment. Upload resolution
and the rclone adapter share this validation. -/
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

/-- Whether a working rclone is available on PATH. -/
def rcloneAvailable : IO Bool := do
  try
    -- Validate concurrency settings during the upload, after tool selection.
    let out ← IO.Process.output {
      cmd := "rclone"
      args := #["version"]
      env := #[("RCLONE_TRANSFERS", none), ("RCLONE_CHECKERS", none)] }
    return out.exitCode == 0
  catch _ =>
    return false

/-- The rclone flags every `put` transfer carries. `--s3-no-check-bucket`
skips the bucket-creation probe a scoped credential cannot pass. -/
def rcloneCommonFlags : Array String := #["--s3-no-check-bucket", "--retries", "5"]

/-- Copy the listed files to the resolved location. `--no-traverse` uses per-file
checks to avoid listing a large destination. A trailing slash marks the destination
as a directory. Non-overwrite uploads skip existing objects. -/
def rcloneFilesArgs (dest : Location) (srcDir filesFrom : FilePath)
    (overwrite : Bool) : Except String (Array String) := do
  let (_, bucketPath) ← s3EndpointSplit dest.root
  return #["copy", srcDir.toString, s!":s3:{bucketPath}/{dest.filesDir}/",
    "--files-from", filesFrom.toString, "--no-traverse"] ++
    (if overwrite then #[] else #["--ignore-existing"]) ++ rcloneCommonFlags

/--
The rclone invocation for the per-SHA marker: a single-file copy to the
marker path. A marker's content is the SHA that names it, so an overwrite is
safe and the copy omits `--ignore-existing`, like the curl tool's marker
put. The bucket and relative path come from the resolved marker.
-/
def rcloneMarkerArgs (marker : Location.Marker) (markerFile : FilePath) :
    Except String (Array String) := do
  let (_, bucketPath) ← s3EndpointSplit marker.root
  return #["copyto", markerFile.toString, s!":s3:{bucketPath}/{marker.path}"] ++
    rcloneCommonFlags

/-- Upload the named staged files, then the location's marker if present.
`env` carries the credentials and endpoint. `RCLONE_TRANSFERS` and `RCLONE_CHECKERS`
default to 128; rclone parses the caller's values.
File failures exit with code 1; marker failures only warn. -/
def putStagedViaRclone (dest : Location) (env : Array (String × Option String))
    (srcDir : FilePath) (fileNames : Array String) (overwrite : Bool)
    (rclone : String := "rclone") : IO Unit := do
  discard <| IO.ofExcept (s3EndpointSplit dest.root)
  let env := env ++ #[
    ("RCLONE_TRANSFERS", some ((← getEnvNonEmpty "RCLONE_TRANSFERS").getD "128")),
    ("RCLONE_CHECKERS", some ((← getEnvNonEmpty "RCLONE_CHECKERS").getD "128"))]
  let run (args : Array String) : IO UInt32 := do
    let child ← IO.Process.spawn { cmd := rclone, args, env }
    child.wait
  if fileNames.isEmpty then
    IO.println "No files to upload"
  else
    IO.println s!"Uploading {fileNames.size} file(s) via rclone to \
      {dest.root}/{dest.filesDir}"
    let dir ← IO.FS.createTempDir
    let code ← try
      let filesFrom := dir / "files-from.txt"
      IO.FS.writeFile filesFrom ("\n".intercalate fileNames.toList ++ "\n")
      run (← IO.ofExcept (rcloneFilesArgs dest srcDir filesFrom overwrite))
    finally
      IO.FS.removeDirAll dir
    if code != 0 then
      IO.eprintln s!"rclone upload failed with exit code {code}"
      IO.Process.exit 1
  uploadMarker dest fun marker file => do
    let code ← run (← IO.ofExcept (rcloneMarkerArgs marker file))
    unless code == 0 do
      throw <| IO.userError s!"rclone exited with code {code}"

end Cache.Requests
